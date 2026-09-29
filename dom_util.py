#!/usr/bin/env python3
"""
dom_util.py — record a Playwright flow by hand and capture the DOM tree at every step.

    python dom_util.py <name> [url] [--out output] [--full]
    python dom_util.py <url>                      (name is taken from the host)

Opens Chromium with Playwright's recorder (the same one `playwright codegen` uses).
Record your flow manually, then close the browser (or press Ctrl+C).

  recordings/<name>.py                      the recorded Playwright script
  output/<name>/<timestamp>/report.md       one row per captured step
  output/<name>/<timestamp>/step-NNN/
      dom-tree.json                         full DOM tree; every node has its absolute XPath,
                                            the element you acted on has "target": true
      step.json                             event + target details + XPath/CSS candidates, each
                                            verified against the live DOM (match count, same element?)
    with --full, also:
      dom-tree.txt                          the same tree as indented text
      target-context.txt                    path from <body> to the target + its surroundings
      page.html                             raw HTML at that moment (password values redacted)

A step is captured on every left click (or keyboard activation), the first keystroke into a
text field, Enter/Tab/Escape, select/checkbox/file changes, and top-frame page loads. Capture
runs in the page's own event listener, before the page reacts, so the tree is the DOM the
element was located in. The page is only read, never modified.

"Best locator" is the strongest candidate that matched exactly one element, the same element
you acted on. Absolute paths, class names, and type-only selectors stay in step.json but are
never chosen as best.

Requires: pip install playwright && playwright install chromium
"""

import argparse
import json
import os
import re
import sys
import threading
import traceback
from datetime import datetime
from pathlib import Path
from urllib.parse import urlparse

BINDING = "__domutilCapture"
MAX_STEPS = 5000
MAX_HTML = 2_000_000

# Kinds that are unique on the page but still a poor thing to automate with.
WEAK_KINDS = {"type", "class", "absolute"}
KIND_RANK = {
    "testid": 0, "id": 1, "name": 2, "aria-label": 3, "placeholder": 4, "label": 5, "title": 6,
    "alt": 7, "href": 8, "text": 9, "anchored": 10, "context-text": 11,
    "type": 40, "class": 41, "absolute": 50,
}

# Injected into every page and frame (main world, before page scripts run). Captures synchronously
# in capture-phase listeners and hands the result to Python through the BINDING function.
# Sites sometimes patch built-ins, so the few that matter are pinned before any page script runs.
JS_CAPTURE = r"""
(() => {
  const KEY = Symbol.for('dom-util.installed');
  if (window[KEY]) return;
  try { Object.defineProperty(window, KEY, { value: true }); } catch (e) { return; }

  const FULL = __FULL__;
  const BINDING = '__BINDING__';
  const MAX_NODES = 10000;      // tree size cap (the path to the target is always kept)
  const MAX_DEPTH = 200;        // nesting cap, keeps recursion and JSON depth safe
  const TARGET_EXTRA = 300;     // nodes allowed under the target past the cap
  const MAX_VERIFY = 15000;     // elements scanned to count CSS matches
  const HTML_NS = 'http://www.w3.org/1999/xhtml';
  const SKIP = new Set(['script', 'style', 'noscript', 'template', 'link', 'meta', 'head']);
  const KEEP = /^(id|name|type|role|href|src|alt|title|placeholder|for|value|class|action|tabindex|contenteditable|disabled|checked|readonly|aria-[\w-]+|data-[\w-]+)$/;
  const INTERACTIVE = 'button,a,input,select,textarea,summary,label,[role=button],[role=link],[role=checkbox],' +
    '[role=radio],[role=tab],[role=menuitem],[role=option],[role=switch],[role=combobox],' +
    '[contenteditable]:not([contenteditable=false])';
  // Checkbox, radio, select etc. also emit `input` when they toggle; that is not typing.
  const NON_TEXT = new Set(['checkbox', 'radio', 'file', 'button', 'submit', 'reset', 'image', 'range', 'color']);

  // Pinned built-ins.
  const from = Array.from;
  const has = (arr, v) => { for (let i = 0; i < arr.length; i++) if (arr[i] === v) return true; return false; };
  const addListener = EventTarget.prototype.addEventListener;
  const Elem = Element, SR = ShadowRoot, XR = XPathResult;
  const evaluate = Document.prototype.evaluate;
  const qsa = Element.prototype.querySelectorAll, dqsa = Document.prototype.querySelectorAll;
  const fqsa = DocumentFragment.prototype.querySelectorAll;
  const matches = Element.prototype.matches, closest = Element.prototype.closest;
  const getAttr = Element.prototype.getAttribute, hasAttr = Element.prototype.hasAttribute;
  const cssEscape = (window.CSS && CSS.escape) ? CSS.escape.bind(CSS) : (s => String(s).replace(/[^\w-]/g, c => '\\' + c));
  const now = Date.now.bind(Date);

  const norm = s => String(s || '').replace(/\s+/g, ' ').trim();
  const clip = (s, n) => s.length > n ? s.slice(0, n - 1) + '…' : s;
  const keepAttr = n => !n.startsWith('data-pw') && !n.startsWith('data-domutil');
  const xq = s => !s.includes('"') ? `"${s}"` : !s.includes("'") ? `'${s}'`
    : 'concat(' + s.split('"').map(p => `"${p}"`).join(`, '"', `) + ')';
  const cssq = s => '"' + String(s).replace(/\\/g, '\\\\').replace(/"/g, '\\"')
    .replace(/[\u0000-\u001f\u007f]/g, ch => '\\' + ch.charCodeAt(0).toString(16) + ' ') + '"';
  const looksDynamic = v => /\d{4,}|[0-9a-f]{8,}|^:r[0-9a-z]*:?$|^(ember|react|mui|ext-gen|yui_|gwt-|headlessui-|radix-)|[-_]\d+$/i.test(v);
  const hashedClass = c => /^(css|sc|jsx|emotion|makeStyles|jss)-/.test(c) || /^_[A-Za-z0-9]{5,}$/.test(c)
    || /__[A-Za-z0-9]{5,}$/.test(c) || /[a-f0-9]{8,}/i.test(c);
  const isSecret = el => el && el.localName === 'input' && String(el.type || '').toLowerCase() === 'password';
  const attrsOf = (el, filter, max) => {
    const out = {};
    for (const a of from(el.attributes || [])) {
      if (!keepAttr(a.name) || (filter && !filter.test(a.name))) continue;
      out[a.name] = a.name === 'value' && isSecret(el) ? '***' : clip(String(a.value), max);
    }
    return out;
  };

  // XPath step for an element: plain name for HTML, name() test for SVG/MathML etc.
  const stepName = el => (el.namespaceURI === HTML_NS || !el.namespaceURI) ? el.localName : `*[name()='${el.localName}']`;
  // Positional steps for a whole sibling list, computed once per parent (O(n), not O(n²)).
  const siblingSteps = kids => {
    const total = new Map(), seen = new Map();
    for (const k of kids) total.set(k.localName, (total.get(k.localName) || 0) + 1);
    return kids.map(k => {
      const i = (seen.get(k.localName) || 0) + 1;
      seen.set(k.localName, i);
      return total.get(k.localName) > 1 ? `${stepName(k)}[${i}]` : stepName(k);
    });
  };
  // XPath from the document (or from `stopAt`) to `el`; shadow boundaries are marked #shadow-root.
  const xpathOf = (el, stopAt = null) => {
    const parts = [];
    for (let n = el, guard = 0; n && n.nodeType === 1 && n !== stopAt && guard < 5000; guard++) {
      const p = n.parentNode;
      const kids = p && p.children ? from(p.children) : [n];
      const i = kids.indexOf(n);
      parts.unshift(i >= 0 ? siblingSteps(kids)[i] : stepName(n));
      if (p && p.nodeType === 11) { if (stopAt) break; parts.unshift('#shadow-root'); n = p.host; } else n = p;
    }
    return (stopAt ? '' : '/') + parts.join('/');
  };

  const visible = el => {
    try { if (typeof el.checkVisibility === 'function' && !el.checkVisibility({ visibilityProperty: true })) return false; } catch (e) {}
    try { const r = el.getBoundingClientRect(); return r.width > 0 && r.height > 0; } catch (e) { return false; }
  };

  // ---- DOM tree -------------------------------------------------------------------------
  const tree = targetEl => {
    let count = 0, extra = 0, truncated = false;
    const pinned = new Set();   // target + its ancestors, kept even past the caps
    for (let n = targetEl, g = 0; n && n.nodeType === 1 && g < 5000; g++) {
      pinned.add(n);
      n = n.parentElement || (n.parentNode && n.parentNode.host) || null;
    }
    const walk = (el, xpath, depth, underTarget) => {
      const tag = el.localName;
      if (!tag || SKIP.has(tag) || tag.startsWith('x-pw')) return null;
      if (!pinned.has(el)) {
        if (depth > MAX_DEPTH) { truncated = true; return null; }
        if (underTarget) { if (extra >= TARGET_EXTRA) { truncated = true; return null; } extra++; }
        else if (count >= MAX_NODES) { truncated = true; return null; }
      }
      count++;
      const node = { tag, xpath };
      const attrs = attrsOf(el, KEEP, 120);
      if (Object.keys(attrs).length) node.attrs = attrs;
      if (el === targetEl) node.target = true;
      let text = '';
      for (const c of from(el.childNodes)) if (c.nodeType === 3) text += c.nodeValue + ' ';
      text = clip(norm(text), 80);
      if (text) node.text = text;
      if (!visible(el)) node.hidden = true;
      const under = underTarget || el === targetEl;
      // Whole SVG icons are noise, but the path down to a clicked shape has to stay.
      const svgCollapsed = tag === 'svg' && !under;
      if (el.shadowRoot && !svgCollapsed) {
        const kids = from(el.shadowRoot.children), steps = siblingSteps(kids);
        const s = kids.map((c, i) => walk(c, `${xpath}/#shadow-root/${steps[i]}`, depth + 1, under)).filter(Boolean);
        if (s.length) node.shadowRoot = s;
      }
      const kids = from(el.children), steps = siblingSteps(kids);
      const out = [];
      kids.forEach((c, i) => {
        if (svgCollapsed && !pinned.has(c)) return;
        const w = walk(c, `${xpath}/${steps[i]}`, depth + 1, under);
        if (w) out.push(w);
      });
      if (out.length) node.children = out;
      return node;
    };
    const start = document.body || document.documentElement;
    const root = start ? walk(start, xpathOf(start), 0, false) : null;
    return { url: location.href, title: String(document.title || ''), nodeCount: count, truncated, root };
  };

  // Elements Playwright's CSS engine would see: light DOM plus open shadow roots.
  const collectOpen = () => {
    const all = [];
    let truncated = false;
    const visit = root => {
      if (!root || truncated) return;
      const list = root === document ? dqsa.call(document, '*') : fqsa.call(root, '*');
      for (const n of from(list)) {
        all.push(n);
        if (all.length >= MAX_VERIFY) { truncated = true; return; }
        if (n.shadowRoot) visit(n.shadowRoot);
      }
    };
    try { visit(document); } catch (e) { truncated = true; }
    return { all, truncated };
  };

  // ---- Target analysis: XPath/CSS candidates verified against the live DOM ---------------
  const target = el => {
    const tag = el.localName;
    const sname = stepName(el);
    const text = norm(clip(String(el.innerText || el.textContent || ''), 5000));
    const shortText = text && text.length <= 60 ? text : '';
    const root = el.getRootNode ? el.getRootNode() : document;
    const inShadow = root !== document;
    const closed = root instanceof SR && root.mode === 'closed';
    const C = [];
    const add = (kind, strategy, expr) => { if (expr) C.push({ kind, strategy, expr }); };
    const xp = (kind, expr) => { if (!inShadow) add(kind, 'xpath', expr); };   // XPath can't enter shadow DOM
    const tstep = shortText ? `${sname}[normalize-space()=${xq(shortText)}]` : sname;
    const attempt = fn => { try { fn(); } catch (e) {} };   // one bad candidate never loses the rest

    attempt(() => {
      for (const a of ['data-testid', 'data-test-id', 'data-test', 'data-qa', 'data-cy', 'data-automation-id']) {
        const v = getAttr.call(el, a);
        if (v) { add('testid', 'css', `[${a}=${cssq(v)}]`); xp('testid', `//*[@${a}=${xq(v)}]`); }
      }
    });
    attempt(() => { if (el.id && !looksDynamic(el.id)) { add('id', 'css', `#${cssEscape(el.id)}`); xp('id', `//*[@id=${xq(el.id)}]`); } });
    attempt(() => {
      const name = getAttr.call(el, 'name');
      if (name && !looksDynamic(name)) { add('name', 'css', `${cssEscape(tag)}[name=${cssq(name)}]`); xp('name', `//${sname}[@name=${xq(name)}]`); }
    });
    attempt(() => {
      for (const a of ['placeholder', 'aria-label', 'title', 'alt']) {
        const v = getAttr.call(el, a);
        if (v) { add(a, 'css', `${cssEscape(tag)}[${a}=${cssq(v)}]`); xp(a, `//${sname}[@${a}=${xq(v)}]`); }
      }
    });
    attempt(() => {
      const labels = el.labels ? from(el.labels) : [];
      if (!labels.length) return;
      const l = labels[0], lt = norm(l.textContent);
      if (!lt || lt.length > 60) return;
      if (l.htmlFor && el.id) xp('label', `//${sname}[@id=//label[normalize-space()=${xq(lt)}]/@for]`);
      else if (l.contains(el)) xp('label', `//label[normalize-space()=${xq(lt)}]//${sname}`);
    });
    if (shortText) xp('text', `//${tstep}`);
    attempt(() => {
      // Repeated components (cards, rows): anchor on nearby distinguishing text.
      for (let anc = el.parentElement, lvl = 0; anc && anc !== document.body && lvl < 5; anc = anc.parentElement, lvl++) {
        const hint = from(qsa.call(anc, 'h1,h2,h3,h4,h5,h6,label,legend,th,td,strong,b,span,p,a')).slice(0, 200).find(n => {
          const t = norm(n.textContent);
          return !n.contains(el) && !el.contains(n) && t && t.length <= 40 && t !== text;
        });
        if (hint) { xp('context-text', `//${stepName(anc)}[.//${stepName(hint)}[normalize-space()=${xq(norm(hint.textContent))}]]//${tstep}`); break; }
      }
    });
    attempt(() => {
      // Anchor on the nearest ancestor with a stable id / test id.
      for (let anc = el.parentElement; anc && anc !== document.body; anc = anc.parentElement) {
        const tAttr = ['data-testid', 'data-test', 'data-qa'].find(a => hasAttr.call(anc, a));
        const aid = anc.id && !looksDynamic(anc.id) ? anc.id : null;
        if (!tAttr && !aid) continue;
        const ancX = aid ? `//*[@id=${xq(aid)}]` : `//*[@${tAttr}=${xq(getAttr.call(anc, tAttr))}]`;
        if (shortText) xp('anchored', `${ancX}//${tstep}`);
        const rel = xpathOf(el, anc);
        if (rel) xp('anchored', `${ancX}/${rel}`);
        break;
      }
    });
    attempt(() => {
      if (tag !== 'a') return;
      const href = getAttr.call(el, 'href');
      if (href && href.length <= 150 && !/^(javascript:|data:)/i.test(href) && !/[?#]/.test(href) && !looksDynamic(href)) {
        add('href', 'css', `a[href=${cssq(href)}]`); xp('href', `//a[@href=${xq(href)}]`);
      }
    });
    attempt(() => { if (tag === 'input' && getAttr.call(el, 'type')) xp('type', `//input[@type=${xq(getAttr.call(el, 'type'))}]`); });
    attempt(() => {
      const classes = from(el.classList || []).filter(c => !hashedClass(c)).slice(0, 2);
      if (classes.length) add('class', 'css', `${cssEscape(tag)}.${classes.map(c => cssEscape(c)).join('.')}`);
    });
    const abs = xpathOf(el);
    xp('absolute', abs);

    const seen = new Set();
    const unique = C.filter(c => { const k = c.strategy + '\0' + c.expr; if (seen.has(k)) return false; seen.add(k); return true; });
    const pageEls = closed ? null : collectOpen();
    const scope = closed ? 'shadow' : 'page';
    const candidates = unique.map(c => {
      try {
        let nodes = [];
        if (c.strategy === 'css') {
          if (!closed && pageEls.truncated) return { ...c, count: null, unique: false, sameElement: false, scope, error: 'page too large to verify CSS' };
          // `[id=...]` counts duplicate ids that `#id` would hide.
          const sel = c.kind === 'id' ? `[id=${cssq(el.id)}]` : c.expr;
          nodes = closed ? from(fqsa.call(root, sel)) : pageEls.all.filter(n => matches.call(n, sel));
        } else {
          const r = evaluate.call(document, c.expr, document, null, XR.ORDERED_NODE_SNAPSHOT_TYPE, null);
          for (let i = 0; i < r.snapshotLength; i++) { const n = r.snapshotItem(i); if (n && n.nodeType === 1) nodes.push(n); }
        }
        const count = nodes.length;
        return { ...c, count, unique: count === 1, sameElement: count === 1 && has(nodes, el), scope };
      } catch (e) {
        return { ...c, count: -1, unique: false, sameElement: false, scope, error: String(e).split('\n')[0] };
      }
    });

    let rect = { x: 0, y: 0, width: 0, height: 0 };
    try { const r = el.getBoundingClientRect(); rect = { x: Math.round(r.x), y: Math.round(r.y), width: Math.round(r.width), height: Math.round(r.height) }; } catch (e) {}
    return { tag, attrs: attrsOf(el, null, 200), text: text.slice(0, 200), xpath: abs, inShadowDom: inShadow,
             shadow: closed ? 'closed' : inShadow ? 'open' : null, visible: visible(el), rect, candidates };
  };

  // ---- Capture --------------------------------------------------------------------------
  const capture = (event, el) => {
    if (!el && (location.href === 'about:blank' || !location.href)) return;
    const send = window[BINDING];
    if (typeof send !== 'function') return;
    const base = { event, url: location.href, isTopFrame: window === window.top, time: new Date().toISOString() };
    let payload;
    try {
      payload = { ...base, target: el ? target(el) : null, tree: tree(el), html: null };
      if (FULL) { try { payload.html = '<!doctype html>\n' + document.documentElement.outerHTML; } catch (e) {} }
    } catch (e) {
      payload = { ...base, error: 'capture failed: ' + String((e && e.message) || e) };   // still record that it happened
    }
    try { send(payload); } catch (e) { console.warn('[dom-util] could not send snapshot', e); }
  };

  // ---- Event wiring ---------------------------------------------------------------------
  let lastClick = { el: null, t: 0 };
  const typed = new WeakSet();

  const pick = e => {
    let path = [];
    try { path = e.composedPath(); } catch (err) {}
    for (const n of path) if (n && n.localName && String(n.localName).startsWith('x-pw')) return null;   // recorder overlay
    const raw = path.find(n => n instanceof Elem) || (e.target instanceof Elem ? e.target : null);
    if (!raw) return null;
    try { return closest.call(raw, INTERACTIVE) || raw; } catch (err) { return raw; }
  };
  const focused = () => {
    let a = document.activeElement;
    for (let g = 0; a && a.shadowRoot && a.shadowRoot.activeElement && g < 50; g++) a = a.shadowRoot.activeElement;
    return a && a !== document.body && a !== document.documentElement ? a : null;
  };
  const click = el => {
    const t = now();
    if (lastClick.el === el && t - lastClick.t < 350) return;   // second half of a double-click
    lastClick = { el, t };
    capture('click', el);
  };
  // The recorder consumes some input events, so typing is detected from whichever arrives first.
  const onType = e => {
    let el = pick(e);
    if (!el || el === document.body || el === document.documentElement) el = focused();
    if (!el || el.localName === 'select' || NON_TEXT.has(el.type)) return;
    if (!typed.has(el)) { typed.add(el); capture('fill', el); }
  };
  // Only real user input (isTrusted) counts; events the page fakes with dispatchEvent are ignored.
  const listen = (type, fn) => addListener.call(window, type, e => {
    try { if (e.isTrusted) fn(e); } catch (err) { console.warn('[dom-util]', err); }
  }, { capture: true, passive: true });

  listen('pointerdown', e => { if (e.button === 0) { const el = pick(e); if (el) click(el); } });
  listen('click', e => { if (e.detail === 0) { const el = pick(e); if (el && el !== document.body) click(el); } });   // Space/Enter activation
  listen('keydown', e => {
    if (e.key === 'Enter' || e.key === 'Tab' || e.key === 'Escape') { const el = pick(e) || focused(); if (el) capture('press ' + e.key, el); }
    else if (e.key && e.key.length === 1 && !e.ctrlKey && !e.metaKey && !e.altKey) onType(e);
  });
  listen('beforeinput', onType);
  listen('input', onType);
  listen('focusout', e => { if (e.target instanceof Elem) typed.delete(e.target); });
  listen('change', e => {
    const el = pick(e);
    if (!el || !(el.localName === 'select' || el.type === 'checkbox' || el.type === 'radio' || el.type === 'file')) return;
    if (lastClick.el === el && now() - lastClick.t < 700) return;   // checkbox: pointerdown already captured it
    capture('change', el);
  });
  const onLoad = () => { if (window === window.top) capture('page-load', null); };
  if (document.readyState === 'complete') setTimeout(onLoad, 0); else addListener.call(window, 'load', onLoad, { once: true });
})();
"""

_PW_ATTR = re.compile(r"""\sdata-pw-[\w-]+=(?:"[^"]*"|'[^']*'|[^\s>]+)""", re.I)
_INPUT_TAG = re.compile(r"""<input\b(?:[^>"']|"[^"]*"|'[^']*')*>""", re.I)
_PASSWORD_TYPE = re.compile(r"""\btype\s*=\s*(?:"password"|'password'|password\b)""", re.I)
INTERACTIVE_TAGS = {"a", "button", "input", "select", "textarea", "label", "option", "summary", "iframe", "form"}


def build_script(full):
    return JS_CAPTURE.replace("__FULL__", "true" if full else "false").replace("__BINDING__", BINDING)


# ------------------------------------------------------------------------------------------
# Text rendering (only used with --full)
# ------------------------------------------------------------------------------------------

def clip(s, n):
    s = s if isinstance(s, str) else str(s)
    return s if len(s) <= n else s[: n - 1] + "…"


def node_line(node, with_xpath=False):
    if not isinstance(node, dict):
        return "?"
    a = node.get("attrs") if isinstance(node.get("attrs"), dict) else {}
    tag = str(node.get("tag") or "?")
    s = tag
    if a.get("id"):
        s += "#" + str(a["id"])
    cls = a.get("class")
    if isinstance(cls, str) and cls:
        s += "".join("." + c for c in cls.split()[:3])
    rest = [f'{k}="{clip(v, 40)}"' for k, v in a.items() if k not in ("id", "class")]
    if rest:
        s += " [" + " ".join(rest) + "]"
    if node.get("text"):
        s += f' "{node["text"]}"'
    if node.get("hidden"):
        s += " (hidden)"
    if node.get("target"):
        s += "   <<< TARGET"
    xpath = node.get("xpath")
    if xpath and (with_xpath or node.get("target") or tag in INTERACTIVE_TAGS or "role" in a or "data-testid" in a):
        s += "   @" + str(xpath)
    return s


def render_tree(node, lines, depth=0, max_depth=None, with_xpath=False):
    """Preorder render. Iterative so a very deep DOM cannot blow the stack."""
    if not isinstance(node, dict):
        return lines
    stack = [("node", node, depth)]
    while stack:
        kind, item, d = stack.pop()
        if kind == "label":
            lines.append(item)
            continue
        pad = "  " * d
        lines.append(pad + node_line(item, with_xpath))
        kids = [c for c in (item.get("children") or []) if isinstance(c, dict)]
        shadow = [c for c in (item.get("shadowRoot") or []) if isinstance(c, dict)]
        if max_depth is not None and d >= max_depth:
            if kids or shadow:
                lines.append(f"{pad}  … {len(kids) + len(shadow)} more child element(s)")
            continue
        for c in reversed(kids):
            stack.append(("node", c, d + 1))
        if shadow:
            for c in reversed(shadow):
                stack.append(("node", c, d + 2))
            stack.append(("label", pad + "  #shadow-root", 0))
    return lines


def find_target_path(node):
    if not isinstance(node, dict):
        return None
    stack = [(node, ())]
    while stack:
        cur, base = stack.pop()
        here = base + (cur,)
        if cur.get("target"):
            return here
        for key in ("children", "shadowRoot"):
            group = cur.get(key) or []
            if isinstance(group, list):
                stack.extend((c, here) for c in reversed(group) if isinstance(c, dict))
    return None


def render_target_context(root):
    path = find_target_path(root) if root else None
    if not path:
        return "No target element for this step.\n"
    anchor = max(0, len(path) - 3)
    lines = ["## Ancestors (body → grandparent)"]
    lines += ["  " * i + node_line(n, True) for i, n in enumerate(path[:anchor])]
    lines += ["", "## Surrounding subtree (grandparent → target and siblings)"]
    render_tree(path[anchor], lines, max_depth=6, with_xpath=True)
    return "\n".join(lines) + "\n"


def describe(t):
    if not isinstance(t, dict):
        return "?"
    a = t.get("attrs") if isinstance(t.get("attrs"), dict) else {}
    bits = [str(t.get("tag") or "?")]
    bits += [f'{k}="{clip(a[k], 30)}"' for k in ("id", "name", "data-testid", "aria-label", "placeholder") if a.get(k)]
    text = t.get("text")
    return "<" + " ".join(bits) + ">" + (f' "{clip(text, 40)}"' if text else "")


# ------------------------------------------------------------------------------------------
# Best-locator choice and file helpers
# ------------------------------------------------------------------------------------------

def _verified_page(c):
    return (
        isinstance(c, dict)
        and c.get("expr")
        and c.get("unique") is True
        and c.get("sameElement") is True
        and not c.get("error")
        and c.get("scope", "page") == "page"
    )


def choose_best(candidates):
    """(best_expr, best_xpath): strongest page-level locator that resolved to exactly the acted-on
    element. Absolute paths, classes, and type-only selectors are never returned as best."""
    if not isinstance(candidates, list):
        return None, None
    good = [c for c in candidates if _verified_page(c)]
    good.sort(key=lambda c: (KIND_RANK.get(c.get("kind"), 30), 0 if c.get("strategy") == "css" else 1))
    strong = [c for c in good if c.get("kind") not in WEAK_KINDS]
    best = strong[0]["expr"] if strong else None
    best_xpath = next((c["expr"] for c in strong if c.get("strategy") == "xpath"), None)
    return best, best_xpath


def redact_secrets(html):
    """Replace password input values, whatever the attribute order or quote style."""
    def repl(m):
        tag = m.group(0)
        if not _PASSWORD_TYPE.search(tag):
            return tag
        tag = re.sub(r'(\bvalue\s*=\s*")[^"]*"', r'\1***"', tag, count=1, flags=re.I)
        tag = re.sub(r"(\bvalue\s*=\s*')[^']*'", r"\1***'", tag, count=1, flags=re.I)
        return re.sub(r"(\bvalue\s*=\s*)([^\s\"'=<>`]+)", r"\1***", tag, count=1, flags=re.I)

    return _INPUT_TAG.sub(repl, html)


def prepare_html(html):
    if not isinstance(html, str) or not html:
        return ""
    html = _PW_ATTR.sub("", html)
    note = ""
    if len(html) > MAX_HTML:
        html, note = html[:MAX_HTML], "\n<!-- dom-util: truncated -->\n"
    return redact_secrets(html) + note


def _md(s):
    return str(s if s is not None else "—").replace("|", "\\|").replace("`", "'").replace("\n", " ")


def write_text(path, text):
    """Atomic write, so an interrupted run never leaves a half-written file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    os.replace(tmp, path)


def write_json(path, obj):
    write_text(path, json.dumps(obj, indent=2, ensure_ascii=False) + "\n")


# ------------------------------------------------------------------------------------------
# Capture sink
# ------------------------------------------------------------------------------------------

class Capture:
    def __init__(self, run_dir, full=False):
        self.run_dir = Path(run_dir)
        self.full = full
        self.steps = []
        self._capped = False
        self._lock = threading.Lock()

    def __call__(self, source, payload):
        # Never call back into the page from here: the page is waiting on this binding.
        del source
        with self._lock:
            try:
                self._save(payload)
            except Exception as e:  # one bad snapshot must not break the recording
                print(f"[dom-util] failed to save snapshot: {e}")

    def _save(self, p):
        if len(self.steps) >= MAX_STEPS:
            if not self._capped:
                print(f"[dom-util] snapshot cap ({MAX_STEPS}) reached; further events are ignored.")
                self._capped = True
            return
        if not isinstance(p, dict):
            raise TypeError("snapshot payload was not an object")
        n = len(self.steps) + 1
        d = self.run_dir / f"step-{n:03d}"
        t = p.get("target") if isinstance(p.get("target"), dict) else None
        dom = p.get("tree") if isinstance(p.get("tree"), dict) else {}
        root = dom.get("root") if isinstance(dom.get("root"), dict) else None
        best, best_xpath = choose_best(t.get("candidates") if t else None)
        url = str(p.get("url") or "")
        step = {
            "step": n,
            "event": p.get("event"),
            "time": p.get("time"),
            "url": url,
            "frame": "main" if p.get("isTopFrame") else url,
            "element": describe(t) if t else None,
            "best": best,
            "bestXpath": best_xpath,
            "target": t,
        }
        if p.get("error"):
            step["error"] = str(p["error"])
        write_json(d / "step.json", step)
        write_json(d / "dom-tree.json", dom)
        if self.full:
            header = [f"# {dom.get('title') or ''} — {dom.get('url') or url}",
                      f"# {dom.get('nodeCount', 0)} elements{' (truncated)' if dom.get('truncated') else ''}", ""]
            write_text(d / "dom-tree.txt", "\n".join(render_tree(root, header) if root else header) + "\n")
            write_text(d / "target-context.txt", render_target_context(root))
            write_text(d / "page.html", prepare_html(p.get("html")))
        self.steps.append(step)

        where = f" on {step['element']}" if t else f" {url}"
        print(f"[dom-util] #{n} {step['event']}{where}")
        if step.get("error"):
            print(f"           {step['error']}")
        if best:
            print(f"           best: {best}")
        if best_xpath and best_xpath != best:
            print(f"           best xpath: {best_xpath}")
        if t and t.get("inShadowDom") and not best:
            print("           inside shadow DOM; no unique page-level locator")

    def write_report(self, recording):
        with self._lock:
            steps = list(self.steps)
        code = lambda v: f"`{_md(v)}`" if v else "—"  # noqa: E731
        lines = [
            "# DOM-UTIL recording", "", f"Script: `{recording}`  ", f"Steps captured: {len(steps)}", "",
            "| # | Event | Element | Frame | Best locator | Best XPath | Files |",
            "|---|---|---|---|---|---|---|",
        ]
        for s in steps:
            name = f"step-{s['step']:03d}"
            files = f"[tree]({name}/dom-tree.json) [step]({name}/step.json)"
            if self.full:
                files += f" [txt]({name}/dom-tree.txt) [context]({name}/target-context.txt)"
            lines.append(
                f"| {s['step']} | {_md(s.get('event'))} | {_md(s.get('element'))} | {_md(s.get('frame'))} | "
                f"{code(s.get('best'))} | {code(s.get('bestXpath'))} | {files} |"
            )
        report = self.run_dir / "report.md"
        write_text(report, "\n".join(lines) + "\n")
        return report


# ------------------------------------------------------------------------------------------
# Browser session
# ------------------------------------------------------------------------------------------

def attach(context, capture, script=None, full=False):
    """Wire DOM capture (and, if `script` is given, Playwright's recorder) into a browser context."""
    context.expose_binding(BINDING, capture)
    context.add_init_script(build_script(full))
    if script is None:
        return
    try:
        # Playwright's built-in recorder (what `playwright codegen` runs). Not a public API.
        context._sync(context._impl_obj._channel.send("enableRecorder", None, {
            "language": "python", "mode": "recording", "outputFile": str(script),
        }))
    except Exception as e:
        print(f"[dom-util] WARNING: couldn't start the Playwright recorder ({e}).\n"
              f"           DOM capture still works; no script will be written.")


def wait_until_closed(browser, context):
    """Block until every tab is closed or the browser goes away. A crashed tab doesn't hang this."""
    from playwright.sync_api import TimeoutError as PWTimeout

    while browser.is_connected():
        pages = [pg for pg in context.pages if not pg.is_closed()]
        if not pages:
            return
        try:
            pages[0].wait_for_event("close", timeout=1000)
        except PWTimeout:
            continue
        except Exception:
            if not browser.is_connected():
                return


def normalize_url(url):
    if url and not re.match(r"^[a-z][a-z0-9+.-]*:", url, re.I):
        return "https://" + url  # "google.com" → "https://google.com"
    return url


def resolve_name(name, url):
    """Accepts `<name> [url]` or just `<url>`; returns a safe file name and the URL."""
    name = (name or "").strip()
    if url is None and re.match(r"^[a-z][a-z0-9+.-]*://", name, re.I):
        url, name = name, urlparse(name).hostname or "recording"
    base = re.sub(r"[^\w.-]+", "_", name.removesuffix(".py")).strip("._-")
    return base or "recording", url


def make_run_dir(parent, stamp=None):
    parent = Path(parent)
    parent.mkdir(parents=True, exist_ok=True)
    stamp = stamp or datetime.now().strftime("%Y-%m-%dT%H-%M-%S")
    for i in range(1, 1000):
        d = parent / (stamp if i == 1 else f"{stamp}-{i}")
        try:
            d.mkdir()
            return d
        except FileExistsError:
            continue
    raise SystemExit(f"Could not create a run directory in {parent}")


def record(name, url, out, full=False):
    try:
        from playwright.sync_api import sync_playwright
    except ImportError:
        raise SystemExit("Playwright is not installed. Run: pip install playwright && playwright install chromium")

    script = Path("recordings").resolve() / f"{name}.py"
    script.parent.mkdir(parents=True, exist_ok=True)
    run_dir = make_run_dir(Path(out).resolve() / name)
    capture = Capture(run_dir, full)

    try:
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=False)
            try:
                context = browser.new_context()
                attach(context, capture, script, full)
                print(f"[dom-util] script    → {script}\n[dom-util] snapshots → {run_dir}\n"
                      f"[dom-util] record your flow, then close the browser (or Ctrl+C).")
                page = context.new_page()
                if url:
                    try:
                        page.goto(normalize_url(url))
                    except Exception as e:
                        print(f"[dom-util] could not open {url}: {str(e).splitlines()[0]}\n"
                              f"[dom-util] the browser is still open; navigate manually.")
                wait_until_closed(browser, context)
            finally:
                try:
                    browser.close()
                except Exception:
                    pass
    except KeyboardInterrupt:
        print("\n[dom-util] stopped.")
    except Exception as e:
        print(f"[dom-util] recording stopped: {e}")
        traceback.print_exc()
    finally:
        try:
            print(f"[dom-util] {len(capture.steps)} steps captured. report → {capture.write_report(script)}")
        except Exception as e:
            print(f"[dom-util] could not write the report: {e}")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("name", help="recording name (script saved to recordings/<name>.py), or a URL")
    ap.add_argument("url", nargs="?", help="start URL")
    ap.add_argument("--out", default="output", help="snapshot output root (default: output)")
    ap.add_argument("--full", action="store_true", help="also write dom-tree.txt, target-context.txt and page.html")
    a = ap.parse_args(argv)
    try:
        sys.stdout.reconfigure(line_buffering=True)  # live progress even when output is piped
    except Exception:
        pass
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 10000))  # deep DOM → deeply nested JSON
    name, url = resolve_name(a.name, a.url)
    record(name, url, a.out, a.full)


if __name__ == "__main__":
    main()
