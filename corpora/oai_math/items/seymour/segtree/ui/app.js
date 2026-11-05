'use strict';

// files come from the server (/files) — the full self-contained src/ tree,
// folders and all. FILES = every file (relative paths like "figures/pruning.tex");
// TEXFILES = the .tex ones that can hold boxes.
let FILES = [];
let TEXFILES = [];
const SRC = {};                 // file -> raw text
let curFile = 'main.tex';
let mode = 'create';            // 'create' | 'select'
let curSel = null;              // {file, s, e}
let dirty = false;

// box: {id, pieces:[{file,s,e},...], children}. A box's region is a LIST of
// pieces, so it can be DISCONTINUOUS and span multiple files. root is a virtual
// container with no pieces.
let ROOT = { id: 'root', pieces: [], children: [] };
let activeId = 'root';          // AMBER: the active LEVEL — where new boxes nest;
                                // drives the PDF focus (black vs grey).
let selId = null;               // BLUE: the currently SELECTED box — the target
                                // of EXTEND. Set by clicking a box (tex or tree);
                                // persists across file/tab switches.
const COLLAPSED = {};
let idCounter = 1;
const freshId = () => 'b' + (idCounter++);

const $ = (x) => document.getElementById(x);
// each box gets its OWN distinct hue from its numeric id (golden-ratio spread),
// so siblings never collide. Same hue is used in the tree, the source tint, and
// the PDF — one box, one color, everywhere.
// one hue per box (golden-ratio spread so siblings never collide), L=50% S=72%
// used IDENTICALLY everywhere (tree swatch, source tint, PDF) so a box is the
// same colour in all three panes.
function boxHue(id) { const n = parseInt(String(id).replace(/\D/g, ''), 10) || 0; return Math.round((n * 137.508) % 360); }
function boxColor(id) { return `hsl(${boxHue(id)} 72% 50%)`; }

/* ================================================= tree helpers */
function walk(n, fn, d = 0) { fn(n, d); n.children.forEach((c) => walk(c, fn, d + 1)); }
function find(id) { let f = null; walk(ROOT, (n) => { if (n.id === id) f = n; }); return f; }
function depthOf(id) { let d = -1; walk(ROOT, (n, dd) => { if (n.id === id) d = dd; }); return d; }
function parentOf(id) { let p = null; walk(ROOT, (n) => { if (n.children.some((c) => c.id === id)) p = n; }); return p; }

// ---- piece / region helpers (a box's region is box.pieces) ----
function pieces(b) { return b.pieces || []; }
// total char length of a box's region (for "narrowest/innermost" comparisons)
function regionLen(b) { return pieces(b).reduce((t, p) => t + (p.e - p.s), 0); }
// does box b cover the char range [s,e) in `file`? (inside ANY one piece)
function covers(b, file, s, e) { return pieces(b).some((p) => p.file === file && p.s <= s && e <= p.e); }
// is span [s,e) in `file` fully inside box b (within one of its pieces)?
function inside(b, file, s, e) { return covers(b, file, s, e); }
// the files a box touches
function boxFiles(b) { return [...new Set(pieces(b).map((p) => p.file))]; }

/* ================================================= file tree (folders) */
// Build a nested folder structure from the flat relative paths, then render it
// as an indented tree — identical layout to src/ (so figures/pruning.tex shows
// under a figures/ folder, not flattened).
function buildFileTree() {
  const root = {};                        // nested dict: name -> subdict | true(file)
  FILES.forEach((rel) => {
    const parts = rel.split('/');
    let node = root;
    parts.forEach((p, i) => {
      if (i === parts.length - 1) node[p] = rel;           // leaf = full rel path
      else node = (node[p] = node[p] || {});
    });
  });
  const host = $('filetree'); host.innerHTML = '';
  host.appendChild(fileTreeLevel(root, 0));
}
function fileTreeLevel(node, depth) {
  const box = document.createElement('div');
  // folders first, then files, each alphabetical
  const keys = Object.keys(node).sort((a, b) => {
    const fa = typeof node[a] === 'object', fb = typeof node[b] === 'object';
    return fa !== fb ? (fa ? -1 : 1) : a.localeCompare(b);
  });
  keys.forEach((name) => {
    const val = node[name];
    const row = document.createElement('div');
    row.className = 'frow';
    row.style.paddingLeft = (8 + depth * 14) + 'px';
    const icon = document.createElement('span'); icon.className = 'ficon';
    if (typeof val === 'object') {          // folder
      icon.textContent = '▾';
      const label = document.createElement('span'); label.textContent = name + '/';
      row.append(icon, label);
      const kids = fileTreeLevel(val, depth + 1);
      row.onclick = () => { const h = kids.hidden; kids.hidden = !h; icon.textContent = h ? '▾' : '▸'; };
      box.append(row, kids);
    } else {                                 // file (val = rel path)
      icon.textContent = '·';
      const label = document.createElement('span'); label.textContent = name;
      row.append(icon, label);
      row.dataset.file = val;
      if (val === curFile) row.classList.add('cur');
      row.onclick = () => openFile(val);
      box.append(row);
    }
  });
  return box;
}
function openFile(rel) {
  curFile = rel;
  $('filetree').querySelectorAll('.frow.cur').forEach((e) => e.classList.remove('cur'));
  const r = $('filetree').querySelector(`.frow[data-file="${CSS.escape(rel)}"]`);
  if (r) r.classList.add('cur');
  $('curfilelab').textContent = rel;
  renderFile();
}
// render the current file's EXACT bytes, line by line, each char-run a .tok with
// offsets; highlight the boxes of THIS file (active box + its direct children).
function renderFile() {
  const host = $('src'); host.innerHTML = '';
  const text = SRC[curFile] || '';
  // Show EVERY box in this file, tinted (background) by its depth so nesting is
  // visible; the active box is outlined. This is the tex-side visualization.
  const ranges = [];               // {s,e,id,depth,active,len}  (one per PIECE in this file)
  walk(ROOT, (n, d) => {
    if (n === ROOT) return;
    pieces(n).forEach((p) => {
      if (p.file === curFile) ranges.push({ s: p.s, e: p.e, id: n.id, depth: d, active: n.id === activeId, len: regionLen(n) });
    });
  });

  // build line rows
  let line = 1, lineStart = 0;
  const pushLine = (s, e) => {
    const row = document.createElement('div'); row.className = 'ln';
    const num = document.createElement('span'); num.className = 'lnum'; num.textContent = line; row.appendChild(num);
    const code = document.createElement('span'); code.className = 'lsrc';
    // split this line [s,e) at range boundaries that fall inside it
    const bounds = new Set([s, e]);
    ranges.forEach((r) => { if (r.s > s && r.s < e) bounds.add(r.s); if (r.e > s && r.e < e) bounds.add(r.e); });
    const pts = [...bounds].sort((a, b) => a - b);
    for (let k = 0; k < pts.length - 1; k++) {
      const a = pts[k], b = pts[k + 1];
      const span = document.createElement('span'); span.className = 'tok'; span.dataset.s = a; span.dataset.e = b;
      span.textContent = text.slice(a, b);
      const covers = ranges.filter((r) => r.s <= a && b <= r.e);
      if (covers.length) {
        span.style.background = blendHexIds(covers.map((r) => r.id)) + '33';   // ~20% alpha
        span.dataset.cover = JSON.stringify(covers.map((r) => r.id));
        // boundaries: top+bottom border (innermost colour) make the band; a left
        // border where a box starts here, a right border where one ends.
        const inner = covers.reduce((p, q) => (q.len <= p.len ? q : p));
        const col = boxColor(inner.id);
        const sh = ['inset 0 1.5px 0 0 ' + col, 'inset 0 -1.5px 0 0 ' + col];
        const starters = covers.filter((r) => r.s === a);
        const enders = covers.filter((r) => r.e === b);
        if (starters.length) sh.push('inset 2px 0 0 0 ' + boxColor(starters.reduce((p, q) => (q.len <= p.len ? q : p)).id));
        if (enders.length) sh.push('inset -2px 0 0 0 ' + boxColor(enders.reduce((p, q) => (q.len <= p.len ? q : p)).id));
        span._base = sh.join(', ');
        span.style.boxShadow = span._base;
      }
      code.appendChild(span);
    }
    row.appendChild(code); host.appendChild(row);
    line++;
  };
  for (let i = 0; i <= text.length; i++) {
    if (i === text.length || text[i] === '\n') { pushLine(lineStart, i); lineStart = i + 1; if (i < text.length) { /* newline consumed */ } }
  }
  wireHover();
}

// Hover a box's text → outline that whole box (all its pieces across lines).
// Hovering a piece picks the INNERMOST covering box, so nested boxes are
// individually hoverable. The outline is a bold inset ring in the box's colour.
let _hoverId = null;
function wireHover() {
  const host = $('src');
  host.onmousemove = (e) => {
    const tok = e.target.closest && e.target.closest('.tok');
    const ids = tok && tok.dataset.cover ? JSON.parse(tok.dataset.cover) : null;
    if (!ids || !ids.length) { if (_hoverId) setHover(null); return; }
    // innermost = the box with the smallest span among those covering this tok
    let best = ids[0], bw = Infinity;
    ids.forEach((id) => { const n = find(id); const w = n ? regionLen(n) : Infinity; if (w < bw) { bw = w; best = id; } });
    if (best !== _hoverId) setHover(best);
  };
  host.onmouseleave = () => setHover(null);
  // Plain left-click (no drag / no selection) on a box's text -> select that box
  // in the left box-tree panel. A click that made a text selection is left alone
  // (that's how you pick text to create/extend a box).
  host.onclick = (e) => {
    if (e.ctrlKey || e.metaKey) return;
    const sel = window.getSelection();
    if (sel && !sel.isCollapsed) return;            // user selected text -> not a pick
    const tok = e.target.closest && e.target.closest('.tok');
    const ids = tok && tok.dataset.cover ? JSON.parse(tok.dataset.cover) : null;
    if (!ids || !ids.length) return;
    // innermost covering box
    let best = ids[0], bw = Infinity;
    ids.forEach((id) => { const n = find(id); const w = n ? regionLen(n) : Infinity; if (w < bw) { bw = w; best = id; } });
    selectBox(best, true);
  };
}
// Set the BLUE selection (the extend target). Persists across file/tab switches.
// `reveal` also reveals + scrolls the row in the Boxes tab (used when clicking
// from the tex side); clicking a tree row directly doesn't need to re-reveal.
function selectBox(id, reveal) {
  selId = id;
  if (reveal) {
    switchTab('boxes');
    let p = parentOf(id);
    while (p) { COLLAPSED[p.id] = false; p = parentOf(p.id); }
    renderTree();
    const r = [...$('tree').querySelectorAll('.row')].find((x) => x._boxId === id);
    if (r) r.scrollIntoView({ block: 'nearest' });
  } else {
    paintSelectedRow();
  }
  updateSelUI();
}
// repaint which tree row carries the blue .picked class (no full re-render)
function paintSelectedRow() {
  $('tree').querySelectorAll('.row.picked').forEach((r) => r.classList.remove('picked'));
  const r = [...$('tree').querySelectorAll('.row')].find((x) => x._boxId === selId);
  if (r) r.classList.add('picked');
}
function setHover(id) {
  _hoverId = id;
  const host = $('src');
  host.querySelectorAll('.tok').forEach((t) => {
    const ids = t.dataset.cover ? JSON.parse(t.dataset.cover) : [];
    if (id && ids.includes(id)) t.style.boxShadow = (t._base ? t._base + ', ' : '') + 'inset 0 0 0 2px ' + boxColor(id);
    else t.style.boxShadow = t._base || '';
  });
}

/* ================================================= selection -> offsets */
function tokAnc(node) { let x = node.nodeType === 3 ? node.parentElement : node; while (x && !(x.classList && x.classList.contains('tok'))) x = x.parentElement; return x; }
function pointOffset(node, off, side) {
  const a = tokAnc(node); if (!a) return null;
  if (node.nodeType === 3) return +a.dataset.s + off;
  return side === 'end' ? +a.dataset.e : +a.dataset.s;
}
function readSelection() {
  const s = window.getSelection(); if (!s || s.rangeCount === 0 || s.isCollapsed) return null;
  const r = s.getRangeAt(0); const host = $('src');
  if (!host.contains(r.startContainer) || !host.contains(r.endContainer)) return null;
  let a = pointOffset(r.startContainer, r.startOffset, 'start');
  let b = pointOffset(r.endContainer, r.endOffset, 'end');
  if (a == null || b == null) return null;
  if (a > b) [a, b] = [b, a];
  if (a >= b) return null;
  return { file: curFile, s: a, e: b };
}

/* ================================================= create / extend / select */
// sort key for a box among siblings: its earliest piece (file then offset)
function regionStart(b) {
  const ps = pieces(b);
  if (!ps.length) return ['', 0];
  return ps.map((p) => [p.file, p.s]).sort((x, y) => (x[0] < y[0] ? -1 : x[0] > y[0] ? 1 : x[1] - y[1]))[0];
}
function sortChildren(n) { n.children.sort((a, b) => { const [fa, sa] = regionStart(a), [fb, sb] = regionStart(b); return fa < fb ? -1 : fa > fb ? 1 : sa - sb; }); }

async function validateSel(file, s, e) {
  try { return await fetch('/validate', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ file, s, e }) }).then((r) => r.json()); }
  catch (_) { return { ok: false, reason: 'validate failed' }; }
}

// 'n' — create a NEW box from the current selection (one piece to start).
async function makeBox() {
  if (mode !== 'create' || !curSel) return;
  const { file, s, e } = curSel;
  const v = await validateSel(file, s, e);
  if (!v.ok) { flash('✗ invalid span: ' + v.reason); return; }

  // parent = the active box if it contains the selection; else the deepest box
  // that contains it; else root.
  let parent = find(activeId);
  if (!(parent && (parent.id === 'root' || covers(parent, file, s, e)))) parent = null;
  if (!parent) {
    parent = ROOT;
    walk(ROOT, (n) => { if (n !== ROOT && covers(n, file, s, e) && regionLen(n) <= (parent === ROOT ? Infinity : regionLen(parent))) parent = n; });
  }
  if (parent !== ROOT && !covers(parent, file, s, e)) { flash('✗ selection not inside the active box'); return; }

  const box = { id: freshId(), pieces: [{ file, s, e }], children: [] };
  // absorb existing siblings fully inside the new box's single piece
  const abs = parent.children.filter((c) => pieces(c).every((p) => covers(box, p.file, p.s, p.e)));
  parent.children = parent.children.filter((c) => !abs.includes(c));
  box.children = abs;
  parent.children.push(box);
  sortChildren(parent);
  selId = box.id;    // the new box becomes the BLUE selection (ready to extend)
  // active level stays put (segment-within keeps nesting under the same parent).
  markDirty();
  window.getSelection().removeAllRanges(); curSel = null;
  refreshAll();
}

// 'e' — EXTEND the SELECTED (blue) box: append the current selection as another
// piece. Independent of the active level. May span files / be discontinuous.
async function extendBox() {
  if (mode !== 'create' || !curSel) return;
  const box = selId ? find(selId) : null;
  if (!box) { flash('click a box to select it (blue) first, then extend'); return; }
  const { file, s, e } = curSel;
  const v = await validateSel(file, s, e);
  if (!v.ok) { flash('✗ invalid span: ' + v.reason); return; }
  box.pieces.push({ file, s, e });
  markDirty();
  window.getSelection().removeAllRanges(); curSel = null;
  refreshAll();
}

// 'r' — REMOVE the EXACT selected character range from the SELECTED (blue) box.
// Mirror of extend: it subtracts [s,e) from whatever piece(s) overlap it. A
// piece cut in the middle splits into two; a fully-covered piece disappears; a
// partially-covered piece is trimmed. If the box ends up with no pieces, it's
// deleted.
async function removeFromCurrent() {
  if (mode !== 'create' || !curSel) return;
  const box = selId ? find(selId) : null;
  if (!box) { flash('click a box to select it (blue) first'); return; }
  const { file, s, e } = curSel;
  const next = [];
  const remainders = [];       // new pieces this remove would create (to validate)
  let changed = false;
  for (const p of box.pieces) {
    if (p.file !== file || e <= p.s || s >= p.e) { next.push(p); continue; } // no overlap
    changed = true;
    if (s > p.s) { const r = { file, s: p.s, e: Math.min(s, p.e) }; next.push(r); remainders.push(r); }
    if (e < p.e) { const r = { file, s: Math.max(e, p.s), e: p.e }; next.push(r); remainders.push(r); }
    // the overlap [max(s,p.s), min(e,p.e)) is dropped
  }
  if (!changed) { flash('selection does not overlap this box'); return; }
  // every remainder must itself be a clean span (so we never leave a dangling
  // \begin/\end or broken brace that fails to compile).
  for (const r of remainders) {
    const v = await validateSel(r.file, r.s, r.e);
    if (!v.ok) { flash('✗ can’t remove there — leaves a broken span: ' + v.reason); return; }
  }
  box.pieces = next;
  window.getSelection().removeAllRanges(); curSel = null;
  if (box.pieces.length === 0) { deleteBox(box.id); return; }
  markDirty(); refreshAll();
}

function setActive(id) { activeId = id; refreshAll(); }

function deleteBox(id) {
  const p = parentOf(id); if (!p) return;
  const i = p.children.findIndex((c) => c.id === id);
  const removed = p.children[i];
  p.children.splice(i, 1, ...removed.children);        // promote children
  sortChildren(p);
  if (activeId === id) activeId = p.id;
  if (selId === id) selId = null;
  markDirty(); refreshAll();
}

/* ================================================= box tree panel */
function renderTree() {
  const host = $('tree'); host.innerHTML = '';
  host.appendChild(treeRow(ROOT, true));
  // persistent "current level" banner: swatch + name + a way back up
  const a = find(activeId);
  const lab = $('activelab'); lab.innerHTML = '';
  const dot = document.createElement('span'); dot.className = 'lvdot';
  dot.style.background = activeId === 'root' ? '#111' : boxColor(activeId);
  const txt = document.createElement('span'); txt.textContent = activeId === 'root' ? 'paper (top level)' : label(a);
  lab.appendChild(dot); lab.appendChild(txt);
}
// label = text of the box's FIRST piece (+ "…" if it has more pieces)
function label(b) {
  const ps = pieces(b); if (!ps.length) return '(span)';
  const p0 = ps[0];
  const t = (SRC[p0.file] || '').slice(p0.s, p0.e).replace(/\s+/g, ' ').trim();
  return (t.slice(0, 28) || '(span)') + (ps.length > 1 ? ` …+${ps.length - 1}` : '');
}
function treeRow(node, isRoot) {
  const wrap = document.createElement('div'); const row = document.createElement('div');
  row._boxId = node.id;
  const kids = node.children.length > 0, collapsed = !!COLLAPSED[node.id];
  row.className = 'row' + (node.id === activeId ? ' active' : '') + (node.id === selId ? ' picked' : '');
  const tw = document.createElement('span'); tw.className = 'twist' + (kids ? '' : ' leaf');
  tw.textContent = kids ? (collapsed ? '▸' : '▾') : '·';
  if (kids) tw.onclick = (e) => { e.stopPropagation(); COLLAPSED[node.id] = !collapsed; renderTree(); };
  row.appendChild(tw);
  if (!isRoot) { const sw = document.createElement('span'); sw.className = 'rswatch'; sw.style.background = boxColor(node.id); row.appendChild(sw); }
  const name = document.createElement('span'); name.className = 'rname'; name.textContent = isRoot ? 'paper' : label(node); row.appendChild(name);
  if (!isRoot) { const fl = document.createElement('span'); fl.className = 'rfile'; fl.textContent = boxFiles(node).map((f) => f.split('/').pop().replace('.tex', '')).join(',').slice(0, 14); row.appendChild(fl); }
  if (!isRoot) { const del = document.createElement('span'); del.className = 'rdel'; del.textContent = '✕'; del.onclick = (e) => { e.stopPropagation(); deleteBox(node.id); }; row.appendChild(del); }
  row.onclick = () => {
    // jump the file view to this box's first piece
    const p0 = pieces(node)[0];
    if (!isRoot && p0 && p0.file !== curFile) openFile(p0.file);
    // clicking a box ALWAYS sets the BLUE selection (the extend target).
    if (!isRoot) selId = node.id;
    // in select-level mode it ALSO sets the AMBER active level.
    if (mode === 'select') setActive(node.id); else renderTree();
    renderFile(); updateSelUI();
    if (!isRoot && p0) jumpTo(p0.s);
  };
  wrap.appendChild(row);

  // piece sub-rows: each piece of this box is its own navigable item (same box
  // colour). Click a piece -> jump to it; ✕ -> remove just that piece. Shown
  // when a box has more than one piece (a single-piece box is its own row).
  if (!isRoot && pieces(node).length > 1 && !collapsed) {
    const pbox = document.createElement('div'); pbox.className = 'children';
    pieces(node).forEach((p, pi) => {
      const prow = document.createElement('div'); prow.className = 'row piecerow';
      const pad = document.createElement('span'); pad.className = 'twist leaf'; pad.textContent = '·'; prow.appendChild(pad);
      const dot = document.createElement('span'); dot.className = 'rswatch'; dot.style.background = boxColor(node.id); dot.style.opacity = '.6'; prow.appendChild(dot);
      const nm = document.createElement('span'); nm.className = 'rname';
      const txt = (SRC[p.file] || '').slice(p.s, p.e).replace(/\s+/g, ' ').trim();
      nm.textContent = `${pi + 1}. ${txt.slice(0, 22) || '(span)'}`; prow.appendChild(nm);
      const fl = document.createElement('span'); fl.className = 'rfile'; fl.textContent = p.file.split('/').pop().replace('.tex', '').slice(0, 10); prow.appendChild(fl);
      const del = document.createElement('span'); del.className = 'rdel'; del.textContent = '✕'; del.title = 'remove this piece';
      del.onclick = (e) => { e.stopPropagation(); removePiece(node.id, pi); }; prow.appendChild(del);
      prow.onclick = () => { if (p.file !== curFile) openFile(p.file); selId = node.id; renderFile(); updateSelUI(); paintSelectedRow(); jumpTo(p.s); };
      pbox.appendChild(prow);
    });
    wrap.appendChild(pbox);
  }

  if (kids) { const box = document.createElement('div'); box.className = 'children' + (collapsed ? ' hidden' : ''); node.children.forEach((c) => box.appendChild(treeRow(c, false))); wrap.appendChild(box); }
  return wrap;
}
// remove a single piece from a box; if it was the last piece, remove the box.
function removePiece(boxId, pieceIdx) {
  const n = find(boxId); if (!n) return;
  n.pieces.splice(pieceIdx, 1);
  if (n.pieces.length === 0) { deleteBox(boxId); return; }   // no pieces left -> gone
  markDirty(); refreshAll();
}
function jumpTo(offset) {
  const host = $('src');
  const t = [...host.querySelectorAll('.tok')].find((x) => +x.dataset.s <= offset && offset < +x.dataset.e);
  if (t) t.scrollIntoView({ block: 'center', behavior: 'smooth' });
}

/* ================================================= modes + ui */
function setMode(m) { mode = m; $('mode-create').classList.toggle('on', m === 'create'); $('mode-select').classList.toggle('on', m === 'select'); updateSelUI(); }
function updateSelUI() {
  const btn = $('mkbox'), ext = $('extendbox'), rem = $('removebox'), info = $('selinfo');
  const selBox = selId ? find(selId) : null;         // BLUE selection = extend/remove target
  if (mode === 'create' && curSel) {
    btn.disabled = false;
    ext.disabled = !selBox;                           // need a selected (blue) box
    // remove enabled if the selection OVERLAPS any piece of the blue box
    const overlaps = selBox && selBox.pieces.some((p) => p.file === curSel.file && curSel.s < p.e && curSel.e > p.s);
    rem.disabled = !overlaps;
    const lvl = activeId === 'root' ? 'paper' : label(find(activeId));
    info.textContent = `${curSel.file} [${curSel.s},${curSel.e}) · n=new in ${lvl}` +
      (selBox ? ` · e=add to “${label(selBox)}”` : ' · (click a box to pick a target)') +
      (overlaps ? ' · r=remove this selection' : '');
  } else { btn.disabled = true; ext.disabled = true; rem.disabled = true; info.textContent = mode === 'select' ? 'select mode — click a box to set the level' : ''; }
}
function flash(msg) { $('status').textContent = msg; setTimeout(() => { $('status').textContent = ''; }, 3000); }
function refreshAll() { renderFile(); renderTree(); updateSelUI(); }

/* ================================================= PDF */
let pdfDoc = null; const PDF_SCALE = 1.25; const pageEls = {};
// a box's colour as rgb[0..1] and #RRGGBB (same hue as tree swatch / source tint)
function hueRGB(id) { const h = boxHue(id) / 360, s = 0.72, l = 0.5; const f = (n) => { const k = (n + h * 12) % 12; return l - s * Math.min(l, 1 - l) * Math.max(-1, Math.min(k - 3, 9 - k, 1)); }; return [f(0), f(8), f(4)]; }
function rgbToHex(rgb) { return '#' + rgb.map((v) => Math.round(255 * Math.max(0, Math.min(1, v))).toString(16).padStart(2, '0')).join('').toUpperCase(); }
function boxHexColor(id) { return rgbToHex(hueRGB(id)); }
// exact blend: average the rgb of several boxes' colours
function blendHexIds(ids) {
  const acc = [0, 0, 0];
  ids.forEach((id) => { const c = hueRGB(id); acc[0] += c[0]; acc[1] += c[1]; acc[2] += c[2]; });
  return rgbToHex(acc.map((v) => v / ids.length));
}
// blend of #RRGGBB hex strings (average rgb)
function blendHexColors(hexes) {
  if (hexes.length === 1) return hexes[0];
  const acc = [0, 0, 0];
  hexes.forEach((h) => { const n = parseInt(h.slice(1), 16); acc[0] += (n >> 16) & 255; acc[1] += (n >> 8) & 255; acc[2] += n & 255; });
  return rgbToHex(acc.map((v) => v / hexes.length / 255));
}
// The whole PDF is ALWAYS grey (set once in the preamble). We only send the
// spans to COLOUR: the active box -> black, its direct children -> their own
// colour, overlaps -> exact blend. If nothing is selected (active = paper) we
// colour every box. One path, no focus branching.
function selectedSpans() {
  const active = (activeId !== 'root') ? find(activeId) : null;
  // flatten boxes to coloured PIECES {file,s,e,color,len}; len = region length so
  // narrower (inner) boxes win over the active black where they overlap.
  const spans = [];
  const add = (box, color) => pieces(box).forEach((p) => spans.push({ file: p.file, s: p.s, e: p.e, color, len: regionLen(box) }));
  if (active) {
    add(active, '#000000');                                  // level = black
    active.children.forEach((c) => add(c, boxHexColor(c.id)));
  } else {
    walk(ROOT, (n) => { if (n !== ROOT) add(n, boxHexColor(n.id)); });
  }
  // cut into non-overlapping pieces per file; each piece = blend of the narrowest
  // boxes covering it (so a child beats the active black; equal-size overlaps blend).
  const byFile = {};
  spans.forEach((sp) => { (byFile[sp.file] = byFile[sp.file] || []).push(sp); });
  const out = [];
  for (const file of Object.keys(byFile)) {
    const segs = byFile[file];
    const pts = new Set();
    segs.forEach((b) => { pts.add(b.s); pts.add(b.e); });
    const sorted = [...pts].sort((x, y) => x - y);
    for (let k = 0; k < sorted.length - 1; k++) {
      const s = sorted[k], e = sorted[k + 1];
      const cover = segs.filter((b) => b.s <= s && e <= b.e);
      if (!cover.length) continue;
      const minLen = Math.min(...cover.map((b) => b.len));
      const win = cover.filter((b) => b.len === minLen);
      out.push({ file, s, e, color: blendHexColors(win.map((b) => b.color)) });
    }
  }
  return { boxes: out };
}
// snapshot of the last tree that COMPILED CLEANLY — the thing we revert to when
// a new box/piece makes LaTeX fail. The compile is the real validator.
let lastGoodTree = null;
let _rendering = false;

function latexErr(log) {
  // pull the first "! ..." TeX error line for a readable message
  const m = (log || '').split('\n').find((l) => l.startsWith('!'));
  return (m || 'LaTeX compile failed').replace(/^!\s*/, '').slice(0, 120);
}

async function renderPdf() {
  if (_rendering) return;                 // don't overlap compiles
  _rendering = true;
  $('status').textContent = 'compiling…';
  let blob;
  try {
    const r = await fetch('/render', { method: 'POST', headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(selectedSpans()) });
    const ct = r.headers.get('Content-Type') || '';
    if (!ct.includes('pdf')) { const j = await r.json(); throw new Error(latexErr(j.log || j.error)); }
    blob = await r.blob();
  } catch (e) {
    _rendering = false;
    // COMPILE IS TRUTH: this tree doesn't build. Revert to the last good tree,
    // tell the user why, and re-render that so the PDF stays valid.
    if (lastGoodTree && JSON.stringify(ROOT) !== lastGoodTree) {
      ROOT = JSON.parse(lastGoodTree);
      selId = find(selId) ? selId : null;
      flash('✗ that span breaks LaTeX — reverted. ' + e.message);
      markDirty();                        // persist the reverted (valid) tree
      refreshAll();
      renderPdf();                         // re-render the good tree
    } else {
      flash('render failed: ' + e.message);
    }
    return;
  }
  // remember where the user was so a recompile doesn't jump them to the top
  const scroller = $('pdfScroll');
  const prevTop = scroller ? scroller.scrollTop : 0;
  const prevLeft = scroller ? scroller.scrollLeft : 0;
  const url = URL.createObjectURL(blob);
  const lib = window['pdfjs-dist/build/pdf'] || window.pdfjsLib;
  lib.GlobalWorkerOptions.workerSrc = 'https://cdn.jsdelivr.net/npm/pdfjs-dist@3.11.174/build/pdf.worker.min.js';
  pdfDoc = await lib.getDocument(url).promise;
  const host = $('pages'); host.innerHTML = '';
  const dpr = window.devicePixelRatio || 1;
  for (let p = 1; p <= pdfDoc.numPages; p++) {
    const page = await pdfDoc.getPage(p);
    const vp = page.getViewport({ scale: PDF_SCALE });
    const wrap = document.createElement('div'); wrap.className = 'page-wrap';
    wrap.style.width = vp.width + 'px'; wrap.style.height = vp.height + 'px';
    const canvas = document.createElement('canvas');
    canvas.width = Math.floor(vp.width * dpr); canvas.height = Math.floor(vp.height * dpr);
    canvas.style.width = vp.width + 'px'; canvas.style.height = vp.height + 'px';
    const ctx = canvas.getContext('2d'); ctx.scale(dpr, dpr); wrap.appendChild(canvas);
    host.appendChild(wrap); pageEls[p] = { wrap };
    page.render({ canvasContext: ctx, viewport: vp });
    // Ctrl/⌘-click → jump to the source FILE this point came from (SyncTeX).
    wrap.dataset.page = p;
    wrap.addEventListener('click', onPdfCtrlClick);
  }
  URL.revokeObjectURL(url);
  // restore the scroll position (page sizes are identical across recompiles)
  if (scroller) scroller.scrollTo({ top: prevTop, left: prevLeft });
  lastGoodTree = JSON.stringify(ROOT);     // this tree compiles — remember it
  _rendering = false;
  $('status').textContent = 'rendered ✓'; setTimeout(() => { $('status').textContent = ''; }, 1200);
}

// Ctrl/⌘-click a PDF page → SyncTeX reverse-sync to the source FILE, open it in
// the Files tab. File granularity only (always reliable; no offset mapping).
async function onPdfCtrlClick(e) {
  if (!(e.ctrlKey || e.metaKey)) return;
  const wrap = e.currentTarget;
  const page = +wrap.dataset.page;
  const rect = wrap.getBoundingClientRect();
  // click position -> PDF points (top-left origin): divide out the render scale
  const x = (e.clientX - rect.left) / PDF_SCALE;
  const y = (e.clientY - rect.top) / PDF_SCALE;
  let hit;
  try { hit = await fetch('/whereis', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ page, x, y }) }).then((r) => r.json()); }
  catch (_) { return; }
  if (hit && hit.file && SRC[hit.file] !== undefined) { switchTab('files'); openFile(hit.file); }
  else flash('could not locate source for that point');
}

/* ================================================= resizable panes */
function setupSplitters() {
  document.querySelectorAll('.splitter').forEach((sp) => {
    const left = $(sp.dataset.left);
    sp.addEventListener('pointerdown', (e) => {
      e.preventDefault(); sp.setPointerCapture(e.pointerId);
      sp.classList.add('drag'); document.body.classList.add('resizing');
      const startX = e.clientX, startW = left.getBoundingClientRect().width;
      const move = (ev) => { const w = Math.max(120, startW + (ev.clientX - startX)); left.style.flex = '0 0 ' + w + 'px'; };
      const up = (ev) => { sp.releasePointerCapture(ev.pointerId); sp.classList.remove('drag'); document.body.classList.remove('resizing'); sp.removeEventListener('pointermove', move); sp.removeEventListener('pointerup', up); };
      sp.addEventListener('pointermove', move); sp.addEventListener('pointerup', up);
    });
  });
}

/* ================================================= save/load */
// Any change calls markDirty(), which AUTOSAVES (debounced). You never lose work
// on reload; the Save button is just a manual "save now".
let _saveTimer = null, _compileTimer = null;
function markDirty() {
  dirty = true;
  clearTimeout(_saveTimer); _saveTimer = setTimeout(save, 600);
  // auto-compile the PDF too (debounced; the Render button stays as a manual
  // trigger). Rapid edits coalesce into one compile.
  clearTimeout(_compileTimer); _compileTimer = setTimeout(() => renderPdf(), 800);
}
async function save(manual) {
  try {
    const r = await fetch('/save', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(ROOT) });
    if (!r.ok) throw new Error('HTTP ' + r.status); dirty = false;
    if (manual === true) flash('saved ✓'); else { $('status').textContent = 'autosaved'; setTimeout(() => { if (!dirty) $('status').textContent = ''; }, 800); }
  } catch (e) { flash('save failed: ' + e.message); }
}

function switchTab(which) {
  $('tab-boxes').classList.toggle('on', which === 'boxes');
  $('tab-files').classList.toggle('on', which === 'files');
  $('panel-boxes').hidden = which !== 'boxes';
  $('panel-files').hidden = which !== 'files';
}

async function init() {
  const fl = await fetch('/files').then((r) => r.json());
  FILES = fl.files; TEXFILES = fl.tex;
  for (const f of FILES) SRC[f] = await fetch('src/' + f).then((r) => r.text());
  try {
    const t = await fetch('tree.json').then((r) => r.ok ? r.json() : null);
    if (t && t.children) {
      // migrate any legacy single-span boxes {file,s,e} -> {pieces:[...]}
      (function mig(n) {
        if (!n.pieces) n.pieces = (n.file != null) ? [{ file: n.file, s: n.s, e: n.e }] : [];
        delete n.file; delete n.s; delete n.e;
        (n.children || []).forEach(mig);
      })(t);
      ROOT = t;
      walk(ROOT, (n) => { const m = /^b(\d+)$/.exec(n.id || ''); if (m) idCounter = Math.max(idCounter, +m[1] + 1); });
    }
  } catch (_) {}

  buildFileTree();
  $('curfilelab').textContent = curFile;
  setupSplitters();
  refreshAll();

  $('tab-boxes').onclick = () => switchTab('boxes');
  $('tab-files').onclick = () => switchTab('files');
  document.addEventListener('selectionchange', () => { if (mode === 'create') { curSel = readSelection(); updateSelUI(); } });
  $('mode-create').onclick = () => setMode('create');
  $('mode-select').onclick = () => setMode('select');
  $('mkbox').onclick = makeBox;
  $('extendbox').onclick = extendBox;
  $('removebox').onclick = removeFromCurrent;
  $('renderpdf').onclick = renderPdf;
  $('save').onclick = () => save(true);
  document.addEventListener('keydown', (e) => {
    const t = document.activeElement; if (t && (t.tagName === 'INPUT' || t.tagName === 'TEXTAREA' || t.tagName === 'SELECT')) return;
    if (e.key === 'n' && mode === 'create' && curSel) { e.preventDefault(); makeBox(); }
    if (e.key === 'e' && mode === 'create' && curSel) { e.preventDefault(); extendBox(); }
    if (e.key === 'r' && mode === 'create' && curSel) { e.preventDefault(); removeFromCurrent(); }
    if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 's') { e.preventDefault(); save(true); }
    if (e.key === 'Escape' && activeId !== 'root') { const p = parentOf(activeId); if (p) setActive(p.id); }
  });
  window.addEventListener('beforeunload', (e) => { if (dirty) { e.preventDefault(); e.returnValue = ''; } });

  // initial render so the PDF pane isn't empty on load (one-off; edits still use
  // the manual Render button).
  renderPdf();
}
init();
