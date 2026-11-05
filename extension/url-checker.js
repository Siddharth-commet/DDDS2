// url-checker.js — content script
// Finds links in the chat, asks background.js for a verdict, and colours the
// underline: green = safe, red = unsafe, amber = caution, grey = unchecked.
// It only sets data-* attributes (+ a tooltip); the colours come from one
// injected stylesheet, so the message text itself is never rewritten.

(() => {
  const STYLE_ID = '__ddd_url_style__';
  const SCAN_DEBOUNCE_MS = 500;
  const BATCH_MS = 400;
  const RETRY_BACKOFF_MS = 30000;

  const LABELS = {
    safe: 'Looks safe',
    unsafe: 'Unsafe',
    caution: 'Be careful',
    unknown: 'Not verified',
  };

  // Chat apps often wrap outgoing links in a redirector; unwrap to the real target.
  const REDIRECTORS = {
    'l.facebook.com': ['u'],
    'lm.facebook.com': ['u'],
    'l.messenger.com': ['u'],
    'slack-redir.net': ['url'],
    'www.google.com': ['q'], // only for /url
  };

  let enabled = true;
  let observer = null;
  let scanTimer = null;
  let flushTimer = null;
  let retryAfter = 0;

  const verdicts = new Map();  // target URL -> { verdict, reasons }
  const pending = new Set();   // URLs waiting to be sent
  const inFlight = new Set();  // URLs sent, awaiting a reply

  // ------------------------------------------------------------------ styling

  function injectStyle() {
    if (document.getElementById(STYLE_ID)) return;
    const s = document.createElement('style');
    s.id = STYLE_ID;
    s.textContent = `
      a[data-ddd] {
        text-decoration-line: underline !important;
        text-decoration-thickness: 2px !important;
        text-underline-offset: 2px !important;
      }
      a[data-ddd="safe"]    { text-decoration-color: #16a34a !important; text-decoration-style: solid  !important; }
      a[data-ddd="unsafe"]  { text-decoration-color: #dc2626 !important; text-decoration-style: solid  !important; }
      a[data-ddd="caution"] { text-decoration-color: #f59e0b !important; text-decoration-style: solid  !important; }
      a[data-ddd="unknown"] { text-decoration-color: #9ca3af !important; text-decoration-style: solid  !important; }
      a[data-ddd="pending"] { text-decoration-color: #9ca3af !important; text-decoration-style: dotted !important; }
    `;
    document.documentElement.appendChild(s);
  }

  // ------------------------------------------------------------ URL helpers

  function resolveTarget(href) {
    let u;
    try { u = new URL(href, location.href); } catch { return null; }
    if (u.protocol !== 'http:' && u.protocol !== 'https:') return null;

    const params = REDIRECTORS[u.hostname];
    if (params && (u.hostname !== 'www.google.com' || u.pathname === '/url')) {
      for (const p of params) {
        const v = u.searchParams.get(p);
        if (!v) continue;
        try {
          const t = new URL(v);
          if (t.protocol === 'http:' || t.protocol === 'https:') return t.href;
        } catch { /* not a URL, ignore */ }
      }
    }
    return u.href;
  }

  const hostOf = (url) => new URL(url).hostname.toLowerCase();

  // True when the link text shows one site but the href goes to another.
  function textHostMismatch(a, targetHost) {
    const text = (a.textContent || '').trim();
    const m = text.match(/^(?:https?:\/\/)?([a-z0-9][a-z0-9.-]*\.[a-z]{2,})(?:[/?#:]|$)/i);
    if (!m) return false;
    const shown = m[1].toLowerCase().replace(/^www\./, '');
    const real = targetHost.replace(/^www\./, '');
    return shown !== real && !real.endsWith('.' + shown) && !shown.endsWith('.' + real);
  }

  // ----------------------------------------------------------------- painting

  function paint(a, target) {
    let r = verdicts.get(target);
    if (!r) return false;

    if (textHostMismatch(a, hostOf(target))) {
      r = {
        verdict: 'unsafe',
        reasons: ['Link text shows a different site than where it really goes', ...r.reasons],
      };
    }

    a.dataset.ddd = r.verdict;
    const tip = `[DDD] ${LABELS[r.verdict]}${r.reasons.length ? ': ' + r.reasons.join('; ') : ''}`;
    if (!a.title || a.title.startsWith('[DDD]')) a.title = tip;
    return true;
  }

  function clearMarks() {
    document.querySelectorAll('a[data-ddd]').forEach((a) => {
      delete a.dataset.ddd;
      delete a.dataset.dddUrl;
      if (a.title.startsWith('[DDD]')) a.removeAttribute('title');
    });
  }

  // ----------------------------------------------------------------- scanning

  function queue(url) {
    if (inFlight.has(url) || Date.now() < retryAfter) return;
    pending.add(url);
    scheduleFlush(BATCH_MS);
  }

  function scheduleFlush(delay) {
    if (flushTimer) return;
    flushTimer = setTimeout(flush, delay);
  }

  function scan() {
    if (!enabled) return;

    for (const a of document.querySelectorAll('a[href]')) {
      if (a.closest('[contenteditable="true"]')) continue;       // the compose box

      const target = resolveTarget(a.getAttribute('href'));
      if (!target) continue;
      if (hostOf(target) === location.hostname) continue;        // in-app navigation

      // Already handled and final: skip.
      if (a.dataset.dddUrl === target && a.dataset.ddd && a.dataset.ddd !== 'pending') continue;

      a.dataset.dddUrl = target;
      if (!paint(a, target)) {
        a.dataset.ddd = 'pending';
        queue(target);
      }
    }
  }

  function scheduleScan() {
    clearTimeout(scanTimer);
    scanTimer = setTimeout(scan, SCAN_DEBOUNCE_MS);
  }

  async function flush() {
    flushTimer = null;
    if (!enabled || pending.size === 0) return;

    if (!chrome.runtime?.id) { stop(); return; } // extension was reloaded; this script is orphaned

    const urls = [...pending];
    pending.clear();
    urls.forEach((u) => inFlight.add(u));

    let resp = null;
    try {
      resp = await chrome.runtime.sendMessage({ type: 'CHECK_URLS', urls });
    } catch (e) {
      console.warn('[DDD] URL check failed:', e);
    }
    urls.forEach((u) => inFlight.delete(u));

    if (resp?.ok) {
      for (const [url, r] of Object.entries(resp.results)) verdicts.set(url, r);
    } else {
      retryAfter = Date.now() + RETRY_BACKOFF_MS; // links stay grey; a later scan retries
    }
    scan();
  }

  // ---------------------------------------------------------------- lifecycle

  function start() {
    if (observer) return;
    injectStyle();
    observer = new MutationObserver(scheduleScan);
    observer.observe(document.body, {
      childList: true,
      subtree: true,
      attributes: true,
      attributeFilter: ['href'],
    });
    scan();
  }

  function stop() {
    if (observer) { observer.disconnect(); observer = null; }
    clearTimeout(scanTimer);
    clearTimeout(flushTimer);
    flushTimer = null;
    pending.clear();
    try { clearMarks(); } catch { /* page may be unloading */ }
  }

  // Respect the same on/off toggle as the rest of the extension.
  chrome.storage.local.get(['enabled'], (res) => {
    enabled = res.enabled !== false;
    if (enabled) start();
  });

  chrome.storage.onChanged.addListener((changes, area) => {
    if (area !== 'local' || !changes.enabled) return;
    enabled = changes.enabled.newValue !== false;
    if (enabled) start(); else stop();
  });
})();
