'use strict';

let DATA = null, BOXES = null;
let NODES = {}, PARENT = {}, DEPTH = {};
let SCALE = 1.4;
const pageEls = {};
let pdfDoc = null;

// ONE piece of state: the selected node. Everything derives from it.
let selId = null;
const COLLAPSED = {};

const $ = (id) => document.getElementById(id);

function index(n, parent, depth) {
  NODES[n.id] = n;
  PARENT[n.id] = parent ? parent.id : null;
  DEPTH[n.id] = depth;
  n.children.forEach((c) => index(c, n, depth + 1));
}
function ancestry(id) { const c = []; let x = id; while (x != null) { c.unshift(x); x = PARENT[x]; } return c; }
function hasKids(id) { return NODES[id].children.length > 0; }

// The node whose children are currently drawn as boxes: the selection itself
// if it has children, otherwise its parent (so a leaf shows among its siblings).
function containerOf(id) { return hasKids(id) ? id : (PARENT[id] != null ? PARENT[id] : id); }

function depthColor(id) {
  const d = Math.min(5, Math.max(1, DEPTH[id]));
  return getComputedStyle(document.documentElement).getPropertyValue('--d' + d).trim() || '#888';
}
function katex(el) {
  if (window.__noKatex || !window.renderMathInElement) return;
  try {
    window.renderMathInElement(el, {
      delimiters: [{ left: '$$', right: '$$', display: true }, { left: '$', right: '$', display: false }],
      throwOnError: false,
    });
  } catch (e) {}
}

/* =================================================================== PDF */
async function renderPdf() {
  const lib = window['pdfjs-dist/build/pdf'] || window.pdfjsLib;
  lib.GlobalWorkerOptions.workerSrc =
    'https://cdn.jsdelivr.net/npm/pdfjs-dist@3.11.174/build/pdf.worker.min.js';
  pdfDoc = await lib.getDocument('paper.pdf').promise;
  await layoutPages();
}
async function layoutPages() {
  const host = $('pages');
  host.innerHTML = '';
  for (const k of Object.keys(pageEls)) delete pageEls[k];
  const dpr = window.devicePixelRatio || 1;
  for (let p = 1; p <= pdfDoc.numPages; p++) {
    const page = await pdfDoc.getPage(p);
    const vp = page.getViewport({ scale: SCALE });
    const wrap = document.createElement('div');
    wrap.className = 'page-wrap';
    wrap.style.width = vp.width + 'px';
    wrap.style.height = vp.height + 'px';
    const canvas = document.createElement('canvas');
    canvas.width = Math.floor(vp.width * dpr);
    canvas.height = Math.floor(vp.height * dpr);
    canvas.style.width = vp.width + 'px';
    canvas.style.height = vp.height + 'px';
    const ctx = canvas.getContext('2d');
    ctx.scale(dpr, dpr);
    wrap.appendChild(canvas);
    const overlay = document.createElement('div');
    overlay.className = 'overlay';
    wrap.appendChild(overlay);
    host.appendChild(wrap);
    pageEls[p] = { wrap, overlay };
    page.render({ canvasContext: ctx, viewport: vp });
  }
  renderBoxes();
}

/* =============================================================== render */
// Draw the boxes for the children of containerOf(selId); the selected one is
// marked .sel. Everything that is clickable calls select().
function renderBoxes() {
  for (const p of Object.values(pageEls)) p.overlay.innerHTML = '';
  if (selId == null) return;              // nothing selected yet (first paint)
  const container = NODES[containerOf(selId)];
  if (!container) return;
  container.children.forEach((child, i) => {
    const rects = BOXES[child.id];
    if (!rects) return;
    const col = depthColor(child.id);
    const isSel = child.id === selId;
    rects.forEach((r, ri) => {
      const pg = pageEls[r.page];
      if (!pg) return;
      const el = document.createElement('div');
      el.className = 'seg-box' + (isSel ? ' sel' : '');
      el.dataset.id = child.id;
      el.style.left = (r.x * SCALE) + 'px';
      el.style.top = (r.y * SCALE) + 'px';
      el.style.width = (r.w * SCALE) + 'px';
      el.style.height = (r.h * SCALE) + 'px';
      el.style.color = col;              // border + hover tint derive from this
      el.style.borderColor = col;
      if (isSel) el.style.background = 'color-mix(in srgb, ' + col + ' 24%, transparent)';
      el.title = child.label;
      el.onclick = (e) => { e.stopPropagation(); select(child.id); };
      if (ri === 0) {
        const num = document.createElement('span');
        num.className = 'num';
        num.style.background = col;
        num.textContent = (i + 1);
        el.appendChild(num);
      }
      pg.overlay.appendChild(el);
    });
  });
}

function renderTree() {
  const root = $('tree');
  root.innerHTML = '';
  root.appendChild(treeRow(DATA.tree));
}
function treeRow(n) {
  const wrap = document.createElement('div');
  const row = document.createElement('div');
  const kids = n.children.length > 0;
  const collapsed = !!COLLAPSED[n.id];
  row.className = 'row' + (collapsed ? ' collapsed' : '') + (n.id === selId ? ' sel' : '');
  const tw = document.createElement('span');
  tw.className = 'twist' + (kids ? '' : ' leaf');
  if (kids) {
    tw.innerHTML = '<span class="open">▾</span><span class="closed">▸</span>';
    tw.onclick = (e) => { e.stopPropagation(); COLLAPSED[n.id] = !collapsed; renderTree(); };
  } else { tw.textContent = '·'; }
  row.appendChild(tw);
  const name = document.createElement('span');
  name.className = 'name'; name.textContent = n.label;
  row.appendChild(name);
  row.onclick = () => select(n.id);
  wrap.appendChild(row);
  if (kids) {
    const box = document.createElement('div');
    box.className = 'children' + (collapsed ? ' hidden' : '');
    n.children.forEach((c) => box.appendChild(treeRow(c)));
    wrap.appendChild(box);
  }
  return wrap;
}

function renderCrumbs() {
  const host = $('crumbs'); host.innerHTML = '';
  ancestry(selId).forEach((id, i) => {
    if (i) { const s = document.createElement('span'); s.className = 'sep'; s.textContent = '›'; host.appendChild(s); }
    const c = document.createElement('span');
    c.className = 'c' + (id === selId ? ' cur' : '');
    c.textContent = NODES[id].label;
    c.onclick = () => select(id);
    host.appendChild(c);
  });
}

function renderInfo() {
  const n = NODES[selId];
  const host = $('info');
  host.innerHTML = '';
  const src = document.createElement('div');
  src.className = 'info-src';
  src.textContent = n.src ? `${n.src[0]} : ${n.src[1]}–${n.src[2]}` : '';
  host.appendChild(src);
  const title = document.createElement('div');
  title.className = 'info-title';
  title.textContent = n.label;
  host.appendChild(title);
  const body = document.createElement('div');
  if (n.text && n.text.trim()) { body.className = 'info-body'; body.textContent = n.text; }
  else { body.className = 'info-body empty'; body.textContent = '(no text of its own — made of the parts below)'; }
  host.appendChild(body);
  katex(body);

  if (n.children.length) {
    const ph = document.createElement('div');
    ph.className = 'parts-head';
    ph.textContent = `${n.children.length} parts`;
    host.appendChild(ph);
    n.children.forEach((c, i) => host.appendChild(partRow(c, i + 1)));
  }
  const hint = document.createElement('div');
  hint.className = 'hint';
  hint.textContent = n.children.length
    ? 'Click a part (here or a numbered box) to open it. Up / breadcrumb to go back.'
    : 'Smallest segment. Up / breadcrumb / tree to move elsewhere.';
  host.appendChild(hint);
}
function partRow(c, num) {
  const kids = c.children.length > 0;
  const row = document.createElement('div');
  row.className = 'part' + (kids ? '' : ' leaf');
  const pn = document.createElement('span');
  pn.className = 'pnum'; pn.style.background = depthColor(c.id); pn.textContent = num;
  const name = document.createElement('span'); name.className = 'pname'; name.textContent = c.label;
  const arr = document.createElement('span'); arr.className = 'parrow'; arr.textContent = kids ? '›' : '·';
  row.appendChild(pn); row.appendChild(name); row.appendChild(arr);
  row.onclick = () => select(c.id);
  return row;
}

/* =============================================================== select */
// THE one action. Clicking anything — box, tree row, part, crumb — calls this.
function select(id) {
  selId = id;
  // make sure the node is visible in the tree
  ancestry(id).forEach((a) => { if (a !== id) COLLAPSED[a] = false; });
  renderBoxes();
  renderTree();
  renderCrumbs();
  renderInfo();
  $('up').disabled = PARENT[id] == null;
  scrollToNode(id);
  const rowEl = $('tree').querySelector('.row.sel');
  if (rowEl) rowEl.scrollIntoView({ block: 'nearest' });
}

function up() {
  const p = PARENT[selId];
  if (p != null) select(p);
}

function scrollToNode(id) {
  const rects = BOXES[id];
  if (!rects || !rects.length) return;
  const pg = pageEls[rects[0].page];
  if (!pg) return;
  $('pdfScroll').scrollTo({ top: Math.max(0, pg.wrap.offsetTop + rects[0].y * SCALE - 70), behavior: 'smooth' });
}

/* ================================================================= init */
async function init() {
  DATA = await fetch('../segments.json').then((r) => r.json());
  BOXES = await fetch('../boxes.json').then((r) => r.json());
  index(DATA.tree, null, 0);
  await renderPdf();
  Object.keys(NODES).forEach((id) => { if (DEPTH[id] >= 1) COLLAPSED[id] = true; });
  COLLAPSED[DATA.tree.id] = false;
  select(DATA.tree.id);
  $('up').onclick = up;
  $('zoom').oninput = async (e) => { SCALE = parseFloat(e.target.value); await layoutPages(); scrollToNode(selId); };
}
init();
