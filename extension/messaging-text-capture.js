// Injected on the messaging domains declared in manifest.json.
//
// 1. Finds the real message elements on the page (per-site selectors below). It no longer
//    falls back to "all page text", so times, contact names and menus are never captured.
// 2. Stores each new message and sends it to the ML server (via background.js) for a label:
//      safe | low_risk | suspicious | harmful
// 3. Shows that label on the message itself in the chat, as a small badge.
//
// Badges are drawn with a CSS ::after rule driven by a data attribute, so no nodes are
// inserted into the chat app's DOM (safer with React re-renders) and the message text
// the app reports is unchanged.

(() => {
  const SITE = location.hostname;
  const STORAGE_KEY = `messagingCapture:${SITE}`;
  const MAX_STORED = 500;         // cap so storage doesn't grow unbounded
  const MIN_LEN = 2;              // ignore near-empty text
  const MAX_LEN = 2000;           // ignore giant blobs (e.g. a pasted document)
  const SCAN_DEBOUNCE_MS = 800;   // wait for the DOM to settle before capturing
  const PAINT_THROTTLE_MS = 200;  // how quickly badges are (re)applied after the DOM changes
  const CLASSIFY_BATCH = 50;      // messages per request to the ML server
  const RETRY_BACKOFF_MS = 30000; // wait this long after the ML server fails

  const VALID_LABELS = new Set(['safe', 'low_risk', 'suspicious', 'harmful']);
  const LABEL_NAMES = { safe: 'Safe', low_risk: 'Low risk', suspicious: 'Suspicious', harmful: 'Harmful' };

  // ---- settings you may want to change -------------------------------------------------
  // Labels listed here are classified but not shown in the chat,
  // e.g. new Set(['safe']) to only display warnings.
  const HIDDEN_LABELS = new Set();

  // true = don't classify messages you sent yourself (only works where OWN_MESSAGE_SELECTORS
  // has an entry). Leave false while testing with "message yourself".
  const SKIP_OWN_MESSAGES = false;
  const OWN_MESSAGE_SELECTORS = { 'web.whatsapp.com': '.message-out' };

  // Selectors for the element holding the TEXT of a message. Tried in order; the first one
  // that matches any message wins. These depend on each site's markup and can break when
  // the site updates, so keep them here. A site with no entry captures nothing.
  const SITE_SELECTORS = {
    'web.whatsapp.com': ['[data-pre-plain-text] span.selectable-text', 'span.selectable-text.copyable-text'],
    'discord.com': ['[id^="message-content-"]'],
    'app.slack.com': ['.p-rich_text_section'],
  };

  // A message that is only a clock time is never a real message.
  const NOISE_PATTERNS = [/^\d{1,2}:\d{2}(\s?[ap]\.?m\.?)?$/i];
  // --------------------------------------------------------------------------------------

  const STYLE_ID = '__ddd_msg_style__';

  let enabled = true;
  let observer = null;
  let debounceTimer = null;
  let paintTimer = null;
  let classifying = false;
  let retryAfter = 0;
  let warnedNoSelector = false;

  const seenThisSession = new Set();
  const labels = new Map(); // message id -> { label, score, explanation, signals }

  // All storage read-modify-write operations run one at a time, so appending new
  // messages and writing back labels can never overwrite each other.
  let writeChain = Promise.resolve();
  function enqueue(fn) {
    const p = writeChain.then(fn);
    writeChain = p.catch(() => {});
    return p;
  }

  // Small non-cryptographic hash, used only to give each message text an id.
  function hashText(str) {
    let h = 0;
    for (let i = 0; i < str.length; i++) {
      h = (Math.imul(31, h) + str.charCodeAt(i)) | 0;
    }
    return h.toString(36);
  }

  // ------------------------------------------------------------ extraction

  const nodeText = (el) => (el.innerText || el.textContent || '').trim();

  function isCandidate(text) {
    return text.length >= MIN_LEN
      && text.length <= MAX_LEN
      && !NOISE_PATTERNS.some((re) => re.test(text));
  }

  // Returns [{ el, text }] for every real message currently in the page.
  function collectMessageNodes() {
    const selectors = SITE_SELECTORS[SITE];
    if (!selectors) {
      if (!warnedNoSelector) {
        warnedNoSelector = true;
        console.info(`[DDD] No message selector configured for ${SITE}; nothing will be captured. Add one to SITE_SELECTORS.`);
      }
      return [];
    }

    const ownSelector = SKIP_OWN_MESSAGES ? OWN_MESSAGE_SELECTORS[SITE] : null;

    for (const selector of selectors) {
      const nodes = [];
      for (const el of document.querySelectorAll(selector)) {
        if (el.closest('[contenteditable="true"]')) continue; // the compose box
        if (ownSelector && el.closest(ownSelector)) continue;
        const text = nodeText(el);
        if (isCandidate(text)) nodes.push({ el, text });
      }
      if (nodes.length) return nodes;
    }
    return [];
  }

  // --------------------------------------------------------------- storage

  function appendMessages(lines) {
    if (lines.length === 0) return Promise.resolve();

    return enqueue(async () => {
      const stored = await chrome.storage.local.get(STORAGE_KEY);
      const existing = stored[STORAGE_KEY] || [];
      const existingIds = new Set(existing.map((m) => m.id));

      const additions = [];
      for (const text of lines) {
        const id = hashText(text);
        if (seenThisSession.has(id) || existingIds.has(id)) continue;
        seenThisSession.add(id);
        additions.push({
          id,
          site: SITE,
          url: location.href,
          text,
          capturedAt: new Date().toISOString(),
          status: 'pending', // replaced by the ML label
        });
      }
      if (additions.length === 0) return;

      const merged = existing.concat(additions);
      const trimmed = merged.length > MAX_STORED
        ? merged.slice(merged.length - MAX_STORED)
        : merged;

      await chrome.storage.local.set({ [STORAGE_KEY]: trimmed });
    });
  }

  // Newest pending messages first, so what the user is reading gets labelled first.
  function pickPending() {
    return enqueue(async () => {
      const stored = await chrome.storage.local.get(STORAGE_KEY);
      return (stored[STORAGE_KEY] || [])
        .filter((m) => m.status === 'pending')
        .slice(-CLASSIFY_BATCH)
        .map(({ id, text }) => ({ id, text }));
    });
  }

  function applyResults(batch, results) {
    return enqueue(async () => {
      const byId = new Map(results.map((r) => [r.id, r]));
      const batchIds = new Set(batch.map((b) => b.id));

      const stored = await chrome.storage.local.get(STORAGE_KEY);
      const list = stored[STORAGE_KEY] || [];

      for (const m of list) {
        if (!batchIds.has(m.id)) continue;
        const r = byId.get(m.id);
        if (r && VALID_LABELS.has(r.label)) {
          m.status = r.label;
          m.score = r.score;
          m.source = r.source || '';
          m.explanation = r.explanation || '';
          m.signals = r.signals || [];
          m.classifiedAt = new Date().toISOString();
        } else {
          m.status = 'unclassified'; // server skipped it; don't retry forever
        }
      }
      await chrome.storage.local.set({ [STORAGE_KEY]: list });

      rebuildLabels(list);
      schedulePaint();
    });
  }

  // -------------------------------------------------------- classification

  async function requestClassification(batch) {
    try {
      return await chrome.runtime.sendMessage({ type: 'CLASSIFY', items: batch });
    } catch (e) {
      console.warn('[DDD] classify request failed:', e);
      return null;
    }
  }

  async function classifyPending() {
    if (classifying || Date.now() < retryAfter) return;
    classifying = true;
    try {
      while (enabled && chrome.runtime?.id) {
        const batch = await pickPending();
        if (batch.length === 0) break;

        const resp = await requestClassification(batch);
        if (!resp?.ok) {
          retryAfter = Date.now() + RETRY_BACKOFF_MS; // messages stay 'pending'; retried later
          break;
        }
        await applyResults(batch, resp.results);
      }
    } finally {
      classifying = false;
    }
  }

  // --------------------------------------------------- badges in the chat

  function injectStyle() {
    if (document.getElementById(STYLE_ID)) return;
    const s = document.createElement('style');
    s.id = STYLE_ID;
    s.textContent = `
      [data-ddd-msg]::after {
        display: inline-block;
        margin-left: 6px;
        padding: 2px 7px;
        border-radius: 9px;
        font: 600 10px/1.3 system-ui, -apple-system, sans-serif;
        letter-spacing: 0.2px;
        white-space: nowrap;
        vertical-align: middle;
        user-select: none;
      }
      [data-ddd-msg="safe"]::after       { content: "\\2713  Safe";        background: #dcfce7; color: #15803d; }
      [data-ddd-msg="low_risk"]::after   { content: "Low risk";            background: #fef9c3; color: #854d0e; }
      [data-ddd-msg="suspicious"]::after { content: "\\26A0  Suspicious";  background: #ffedd5; color: #c2410c; }
      [data-ddd-msg="harmful"]::after    { content: "\\26D4  Harmful";     background: #fee2e2; color: #b91c1c; }
      [data-ddd-msg="suspicious"] {
        background: rgba(249, 115, 22, 0.22);
        border-radius: 4px;
        box-decoration-break: clone;
        -webkit-box-decoration-break: clone;
      }
      [data-ddd-msg="harmful"] {
        background: rgba(220, 38, 38, 0.28);
        border-radius: 4px;
        box-decoration-break: clone;
        -webkit-box-decoration-break: clone;
      }
    `;
    document.documentElement.appendChild(s);
  }

  function rebuildLabels(list) {
    labels.clear();
    for (const m of list || []) {
      if (VALID_LABELS.has(m.status)) {
        labels.set(m.id, {
          label: m.status,
          score: m.score,
          explanation: m.explanation,
          signals: m.signals,
        });
      }
    }
  }

  function tooltipFor(info) {
    const lines = [`[DDD] ${LABEL_NAMES[info.label]}`
      + (typeof info.score === 'number' ? ` (risk ${Math.round(info.score * 100)}%)` : '')];
    if (info.explanation) lines.push(info.explanation);
    if (Array.isArray(info.signals) && info.signals.length) lines.push(`Signals: ${info.signals.join(', ')}`);
    return lines.join('\n');
  }

  function paintMessage(el, info) {
    if (!info) {
      if (el.dataset.dddMsg) {
        delete el.dataset.dddMsg;
        if ((el.title || '').startsWith('[DDD]')) el.removeAttribute('title');
      }
      return;
    }
    if (el.dataset.dddMsg !== info.label) el.dataset.dddMsg = info.label;
    if (!el.title || el.title.startsWith('[DDD]')) {
      const tip = tooltipFor(info);
      if (el.title !== tip) el.title = tip;
    }
  }

  function paintAll() {
    paintTimer = null;
    if (!enabled) return;
    for (const { el, text } of collectMessageNodes()) {
      const info = labels.get(hashText(text));
      paintMessage(el, info && !HIDDEN_LABELS.has(info.label) ? info : null);
    }
  }

  // Throttled (not debounced) so badges keep up even while the chat is constantly updating.
  function schedulePaint() {
    if (paintTimer) return;
    paintTimer = setTimeout(paintAll, PAINT_THROTTLE_MS);
  }

  function clearMarks() {
    document.querySelectorAll('[data-ddd-msg]').forEach((el) => {
      delete el.dataset.dddMsg;
      if ((el.title || '').startsWith('[DDD]')) el.removeAttribute('title');
    });
  }

  // ------------------------------------------------------------- scanning

  async function scan() {
    if (!enabled) return;
    if (!chrome.runtime?.id) { stopObserving(); return; } // extension reloaded; this script is orphaned
    await appendMessages(collectMessageNodes().map((n) => n.text));
    schedulePaint();
    classifyPending();
  }

  function scheduleScan() {
    clearTimeout(debounceTimer);
    debounceTimer = setTimeout(scan, SCAN_DEBOUNCE_MS);
  }

  function onDomChange() {
    scheduleScan();
    schedulePaint(); // chat apps recreate nodes while scrolling; re-apply badges quickly
  }

  async function startObserving() {
    if (observer) return;
    injectStyle();
    observer = new MutationObserver(onDomChange);
    observer.observe(document.body, {
      childList: true,
      subtree: true,
      characterData: true,
    });
    try {
      const stored = await chrome.storage.local.get(STORAGE_KEY);
      rebuildLabels(stored[STORAGE_KEY]); // labels from earlier visits
    } catch { /* storage unavailable; labels will arrive with new results */ }
    schedulePaint();
    scan(); // capture whatever is already on screen
  }

  function stopObserving() {
    if (observer) {
      observer.disconnect();
      observer = null;
    }
    clearTimeout(debounceTimer);
    clearTimeout(paintTimer);
    paintTimer = null;
    try { clearMarks(); } catch { /* page may be unloading */ }
  }

  chrome.storage.local.get(['enabled'], (res) => {
    enabled = res.enabled !== false;
    if (enabled) startObserving();
  });

  chrome.storage.onChanged.addListener((changes, area) => {
    if (area !== 'local') return;

    if (changes[STORAGE_KEY]) {
      const list = changes[STORAGE_KEY].newValue;
      if (!list || list.length === 0) seenThisSession.clear(); // data was cleared; allow re-capture
      rebuildLabels(list);
      schedulePaint();
    }

    if (changes.enabled) {
      enabled = changes.enabled.newValue !== false;
      if (enabled) startObserving();
      else stopObserving();
    }
  });
})();