/* The LEFT PANEL of the labeler: `Main.lean` itself, verbatim and complete.
 *
 * Nothing is summarized or cut — the signature, the tactics, the claims and the comments are all
 * there, because the natural language being judged *is* the string literals in that file. The only
 * clickable regions are the ones a faithfulness claim lives in — the head of a `pistis_intro` or
 * `pistis_segment`; clicking one loads that unit into the right panel.
 *
 * Wrapped in an IIFE on purpose: this shares a global lexical scope with the labeler's inline script,
 * where `$`, `escapeHtml`, `MATH_RE` and friends are top-level `const`s — a second declaration of any
 * of them would be a redeclaration error and would kill the whole page.
 *
 * window.ProofPane:
 *     mount(host, onOpen)   fetch /api/overview and render into `host`; a click calls onOpen(path)
 *     refresh()             re-fetch and re-render — the progress count follows a save
 *     rerender()            re-render the cached payload (e.g. once Shiki's colours arrive)
 *     setWrap(on)           soft wrap the proof, as alt+Z does in VSCode (remembered)
 *     setCurrent(path)      mark which unit the right panel is showing
 *     firstPath()           the first unit, in proof order, that has a datapoint on disk
 *     locate(main, line)    where a `path:line` citation points, if anywhere  (see below)
 *     revealLine(main,lo,hi) jump the pane to line `lo` and mark `lo..hi`; pushes the back stack
 *     goBack() / canGoBack()   undo one jump: alt+← , and the toolbar's ← button
 *
 * A `C_F` item cites the line of `Main.lean` it was read off (`items/item1/Main.lean:46`), and the
 * right panel makes that citation clickable: it jumps HERE rather than opening anything, because this
 * panel already holds the whole file. `locate` is what lets the citation be rendered honestly —
 * whether the file is on the page at all, how many lines it has — so a citation that resolves to
 * nothing can be marked instead of drawn as a live link. `check_citations.py` is the same check
 * offline, against the signature too.
 */
(function(){
"use strict";

let HOST = null, ONOPEN = null, DATA = null, CURRENT = null;

// soft wrap, like VSCode's alt+Z. On by default; remembered, because it's a reading preference.
const WRAP_KEY = "pistis.wrap";
let WRAP = true;
try{ WRAP = localStorage.getItem(WRAP_KEY) !== "0"; }catch(e){}

const esc = s => String(s).replace(/[&<>"]/g,
  c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));

// ---------------------------------------------------------------------------
// syntax highlighting as a flat list of runs over the RAW source
// ---------------------------------------------------------------------------
// Every click target is a UTF-16 offset into the exact bytes of Main.lean, so highlighting must not
// be allowed to shift anything. Shiki's tokens are flattened to [start, end, colour) runs and then
// checked against the source; if they do not reconstruct it character-for-character the colours are
// dropped rather than risk a misplaced click target.
function styledRuns(src){
  const plain = [{s:0, e:src.length, color:null}];
  if(!window.__shiki || window.__noShiki) return plain;
  let lines;
  try{ lines = window.__shiki.codeToTokens(src, {lang:"lean", theme:"github-light"}).tokens; }
  catch(e){ return plain; }
  const runs = []; let pos = 0;
  lines.forEach((line, li) => {
    for(const t of line){ runs.push({s:pos, e:pos + t.content.length, color:t.color || null});
                          pos += t.content.length; }
    if(li < lines.length - 1){ runs.push({s:pos, e:pos + 1, color:null}); pos += 1; }  // the \n
  });
  return runs.map(r => src.slice(r.s, r.e)).join("") === src ? runs : plain;
}
function runsHtml(src, runs, lo, hi){
  let out = "";
  for(const r of runs){
    if(r.e <= lo || r.s >= hi) continue;
    const text = esc(src.slice(Math.max(r.s, lo), Math.min(r.e, hi)));
    out += r.color ? `<span style="color:${r.color}">${text}</span>` : text;
  }
  return out;
}

// ---------------------------------------------------------------------------
// status of one unit
// ---------------------------------------------------------------------------
// Status is NOT drawn into the proof: a badge after every region broke up the source it was supposed
// to be annotating. It lives in the hover title instead, and in the pane's progress count; the
// verdict itself belongs to the right panel, which is where it is made.
function statusOf(u, itemPath){
  const dp = u.datapoint;
  if(!dp) return {missing: true, text: "no datapoint",
    title: "No datapoint on disk. Run:  python3 faithfulness/gen_datapoints.py " + itemPath};
  const tick = dp.done ? "✓ " : "";
  if(dp.label === "faithful")   return {text: tick + "faithful"};
  if(dp.label === "unfaithful") return {text: tick + "unfaithful"};
  return {text: dp.done ? tick + "no edges" : "unlabeled"};
}

// ---------------------------------------------------------------------------
// one unit's clickable region
// ---------------------------------------------------------------------------
// `last` says whether this is the final fragment of the region (see fileHtml); only that one carries
// the id, so `#pa-<unit>` names the region as a whole.
function anchorHtml(u, item, inner, last){
  const st = statusOf(u, item.path);
  const dp = u.datapoint;
  // A real href, so ctrl/middle-click still opens the unit in its own tab; the delegated handler
  // intercepts the ordinary click and loads it into the right panel instead.
  return `<a class="anchor k-${u.kind}${dp ? "" : " nodp"}`
       + `${dp && dp.path === CURRENT ? " cur" : ""}"`
       + ` data-u="${esc(u.id)}"`              // ties a region's per-line fragments together
       + (last ? ` id="pa-${esc(u.id)}"` : "")
       + (dp ? ` href="/?path=${encodeURIComponent(dp.path)}" data-dp="${esc(dp.path)}"`
             : ` href="#" data-nodp="${esc(st.title)}"`)
       + ` title="${esc(u.id + " · " + u.kind + " · " + st.text
                       + (dp ? "\n" + dp.path : ""))}"`
       + `>${inner}</a>`;
}

// ---------------------------------------------------------------------------
// one item: its Main.lean, verbatim, with the unit regions made clickable
// ---------------------------------------------------------------------------
// Rendered as one grid row per SOURCE line — the number in a gutter cell, the text beside it —
// rather than as a parallel column of numbers next to one <pre>. That is what lets the text soft
// wrap (alt+Z): a wrapped line is taller than one row, so a separate gutter would drift out of step
// with it, while a per-line cell simply grows with its line.
//
// The cost is that a clickable region spanning a line break has to be emitted as one <a> per line.
// They carry the same `data-dp`, so clicking any fragment opens the same unit; only the last one
// gets the id.
function fileHtml(item){
  const src = item.source;
  const runs = styledRuns(src);
  // Anchors come out of pistis_proof.source_anchors non-overlapping and in source order; sort and
  // drop overlaps defensively, so one bad anchor can never corrupt the whole file.
  const anchors = [];
  let last = 0;
  for(const u of item.units.filter(u => u.anchor).sort((a, b) => a.anchor[0] - b.anchor[0])){
    const [a, b] = u.anchor;
    if(a < last || b < a || b > src.length) continue;
    anchors.push({u:u, a:a, b:b});
    last = b;
  }

  const rows = [];
  const body = src.endsWith("\n") ? src.slice(0, -1) : src;   // a trailing \n is not a line of its own
  let pos = 0, next = 0;
  body.split("\n").forEach((line, i) => {
    const ls = pos, le = pos + line.length;
    while(next < anchors.length && anchors[next].b <= ls) next++;   // fully behind us
    let cell = "", at = ls;
    for(let k = next; k < anchors.length && anchors[k].a < le; k++){
      const {u, a, b} = anchors[k];
      const from = Math.max(a, ls), to = Math.min(b, le);
      cell += runsHtml(src, runs, at, from);
      cell += anchorHtml(u, item, runsHtml(src, runs, from, to), b <= le);
      at = to;
    }
    cell += runsHtml(src, runs, at, le);
    // VSCode's `wrappingIndent: same`: a wrapped row lines up under its line's indentation rather
    // than under the gutter, which for a deeply nested tactic block is the difference between
    // readable and not. A hanging indent does it — `--ind` is the line's own indent, the CSS turns
    // it into padding on the block and cancels it on the first row. Capped, so one freakishly
    // indented line cannot squeeze the text column to nothing.
    const ind = Math.min(line.length - line.trimStart().length, 24);
    // `data-line` on both cells of the row: a citation jump has a line NUMBER to find, and the row
    // is the only thing that knows where that line ended up after wrapping.
    rows.push(`<span class="lnum" data-line="${i + 1}">${i + 1}</span>`
            + `<span class="lsrc" data-line="${i + 1}"${ind ? ` style="--ind:${ind}ch"` : ""}>${cell}</span>`);
    pos = le + 1;
  });
  return `<div class="code${WRAP ? "" : " nowrap"}" data-main="${esc(item.main)}">${rows.join("")}</div>`;
}

// ---------------------------------------------------------------------------
// citation jumps, and a back stack
// ---------------------------------------------------------------------------
// Where `path:line` points in what is RENDERED. `file` says whether that file is on the page at all
// (a Mathlib citation is not), `lines` how long it is, `row` the line's own cell. The caller needs
// the three apart to say WHY a citation does not resolve, instead of just failing to scroll.
function locate(main, line){
  const code = HOST && HOST.querySelector(`.code[data-main="${CSS.escape(String(main))}"]`);
  if(!code) return {file:false, lines:0, row:null};
  const rows = code.querySelectorAll(".lsrc");
  return {file:true, lines:rows.length, row:rows[line - 1] || null};
}

// The jump stack. An entry is where the pane was LOOKING, which is a scroll offset plus the unit the
// right panel had open — jumping to a citation of another unit's context and then going back should
// restore both, not just the scroll.
const BACK = [];
const BACK_MAX = 50;
let SUPPRESS_SCROLL = false;    // see goBack: setCurrent scrolls, and here it must not

function clearLit(){
  if(HOST) HOST.querySelectorAll(".lit").forEach(e => e.classList.remove("lit"));
}
function paintBackBtn(){
  const b = HOST && HOST.querySelector("#backBtn");
  if(b){ b.disabled = !BACK.length; b.textContent = "← back" + (BACK.length > 1 ? ` (${BACK.length})` : ""); }
}
// `hi` is for a citation of a RANGE (`Main.lean:37-38`), i.e. a context item read off more than one
// line: every line it quotes is marked, not just the one scrolled to.
function revealLine(main, line, hi){
  const {row} = locate(main, line);
  if(!row) return false;
  BACK.push({top: HOST ? HOST.scrollTop : 0, path: CURRENT});
  if(BACK.length > BACK_MAX) BACK.shift();
  clearLit();
  // The lines stay marked after the jump rather than flashing: the point of the jump is to read the
  // line you cited, and a 400ms flash is gone before the scroll settles.
  const code = row.parentElement;
  for(let n = line; n <= Math.max(line, hi || line); n++)
    code.querySelectorAll(`[data-line="${n}"]`).forEach(e => e.classList.add("lit"));
  if(row.scrollIntoView) row.scrollIntoView({block:"center", behavior:"smooth"});
  paintBackBtn();
  return true;
}
async function goBack(){
  const e = BACK.pop();
  if(!e) return false;
  clearLit();
  // Reopen the unit first if it changed: that re-renders the right panel and calls setCurrent, which
  // scrolls this pane -- so it has to happen BEFORE the scroll offset is put back, and without its
  // own scrolling getting in the way.
  if(e.path && e.path !== CURRENT && ONOPEN){
    SUPPRESS_SCROLL = true;
    try{ await ONOPEN(e.path); }
    finally{ SUPPRESS_SCROLL = false; }
  }
  if(HOST) HOST.scrollTop = e.top;
  paintBackBtn();
  return true;
}

function rerender(){
  if(!HOST || !DATA) return;
  let done = 0, total = 0, missing = 0;
  for(const item of DATA.items)
    for(const u of item.units){
      total++;
      if(u.datapoint && u.datapoint.done) done++;
      if(!u.datapoint) missing++;
    }
  // one toolbar for the whole pane: overall progress, and the wrap toggle
  const bar = `<div class="ptoolbar">
    <span class="mut">the proof — click a <code>pistis_</code> sentence</span>
    <span class="grow"></span>
    <span class="mut">${done}/${total} done${missing ? ` · ${missing} without a datapoint` : ""}</span>
    <button id="backBtn" class="tiny" title="back to where you were before the last citation jump (alt+←)"></button>
    <button id="wrapBtn" class="tiny" title="soft wrap long lines (alt+Z)"></button></div>`;
  const parts = DATA.items.map(item => `<div class="pitem">
      <div class="pitemhead"><b>item${item.index}</b> <code class="mut">${esc(item.main)}</code></div>
      <div class="pitemsub mut">${esc(item.result || item.name)}</div>
      ${fileHtml(item)}</div>`);
  HOST.innerHTML = bar + (parts.join("")
    || '<div class="mut" style="padding:12px">No items with a Main.lean found.</div>');
  HOST.querySelector("#wrapBtn").onclick = () => setWrap(!WRAP);
  HOST.querySelector("#backBtn").onclick = () => goBack();
  paintWrapBtn();
  paintBackBtn();
}

function paintWrapBtn(){
  const b = HOST && HOST.querySelector("#wrapBtn");
  if(b) b.textContent = WRAP ? "⏎ wrap on" : "→ wrap off";
}

// Only one class differs between the two modes, so flip it in place: re-rendering the file would
// throw away the scroll position for what is a purely visual change.
function setWrap(on){
  WRAP = !!on;
  try{ localStorage.setItem(WRAP_KEY, WRAP ? "1" : "0"); }catch(e){}
  if(!HOST) return;
  HOST.querySelectorAll(".code").forEach(c => c.classList.toggle("nowrap", !WRAP));
  paintWrapBtn();
}

async function load(){
  try{
    const r = await fetch("/api/overview");
    const j = await r.json();
    if(j.error){ HOST.innerHTML = `<div class="err">${esc(j.error)}</div>`; return; }
    DATA = j;
  }catch(e){ HOST.innerHTML = `<div class="err">${esc(String(e))}</div>`; return; }
  rerender();
}

window.ProofPane = {
  async mount(host, onOpen){
    HOST = host; ONOPEN = onOpen;
    host.addEventListener("click", ev => {
      const a = ev.target.closest("a.anchor");
      if(!a) return;
      // let the browser do its thing for new-tab / new-window clicks
      if(ev.metaKey || ev.ctrlKey || ev.shiftKey || ev.altKey || ev.button !== 0) return;
      ev.preventDefault();
      if(!a.dataset.dp){ alert(a.dataset.nodp); return; }
      if(ONOPEN) ONOPEN(a.dataset.dp);
    });
    // A region that spans lines is several <a>s, so highlight them as the one thing they are: CSS
    // :hover would light up only the line under the cursor.
    let hov = null;
    const sameUnit = id => host.querySelectorAll(`a.anchor[data-u="${CSS.escape(id)}"]`);
    host.addEventListener("mouseover", ev => {
      const a = ev.target.closest("a.anchor");
      const id = a ? a.dataset.u : null;
      if(id === hov) return;
      if(hov) sameUnit(hov).forEach(x => x.classList.remove("hov"));
      hov = id;
      if(id) sameUnit(id).forEach(x => x.classList.add("hov"));
    });
    // leaving the pane altogether fires no mouseover inside it, so clear explicitly
    host.addEventListener("mouseleave", () => {
      host.querySelectorAll("a.anchor.hov").forEach(x => x.classList.remove("hov"));
      hov = null;
    });
    // alt+Z, as in VSCode. `code` rather than `key`, because alt+z emits a different character on
    // several keyboard layouts (`Ω` on a Mac, for one).
    document.addEventListener("keydown", ev => {
      if(!ev.altKey || ev.ctrlKey || ev.metaKey) return;
      if(ev.code === "KeyZ" || (ev.key || "").toLowerCase() === "z"){
        ev.preventDefault();
        setWrap(!WRAP);
        return;
      }
      // alt+← : undo a citation jump. The browser's own Back is only pre-empted when there IS a jump
      // to undo -- the labeler navigates with replaceState, so nothing of ours is in session history
      // and leaving the page is the reasonable default when the stack is empty.
      if((ev.code === "ArrowLeft" || ev.key === "ArrowLeft") && BACK.length){
        ev.preventDefault();
        goBack();
      }
    });
    await load();
  },
  refresh: load,
  rerender,
  setWrap,
  setCurrent(path){
    if(CURRENT === path) return;
    CURRENT = path;
    if(!HOST) return;
    HOST.querySelectorAll("a.anchor.cur").forEach(a => a.classList.remove("cur"));
    const a = HOST.querySelector(`a.anchor[data-dp="${CSS.escape(path || "")}"]`);
    if(!a) return;
    a.classList.add("cur");
    if(!SUPPRESS_SCROLL && a.scrollIntoView) a.scrollIntoView({block:"nearest"});
  },
  locate,
  revealLine,
  goBack,
  canGoBack(){ return BACK.length > 0; },
  firstPath(){
    for(const item of (DATA ? DATA.items : []))
      for(const u of item.units)
        if(u.datapoint) return u.datapoint.path;
    return null;
  },
};
})();
