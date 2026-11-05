'use strict';
// ───────────────────────────────────────────────────────────────────────────
// PDF-direct segmentation. The PDF is the source.
//
// GLOBAL CHARACTER SEQUENCE: after rendering, we walk every page's text layer
// in reading order and concatenate the glyphs into one string CHARS. CHARMETA[i]
// records, for character i, which page + a function to get its rect, so a span
// of character indices can be drawn as highlight rectangles. A box piece is just
// {start,end} into CHARS. This index is deterministic → exact.
// ───────────────────────────────────────────────────────────────────────────

let CHARS = '';            // the whole paper as one character sequence
let CHARMETA = [];         // CHARMETA[i] = {page, x, y, w, h} glyph rect (PDF.js viewport px)
let pageEls = {};          // page -> {wrap, hl}
let PDF_SCALE = 1.4;

// data: box = {id, pieces:[{start,end}], children}
// ROOT also carries ROOT.links = [{from, to}] — directed arrows between any two
// nodes (by id), drawn on the PDF from the source region to the target region.
let ROOT = { id: 'root', pieces: [], children: [] };
let levelId = 'root';      // CURRENT NODE — new boxes are added as ITS children.
                           // The tree structure is AUTHORED via this, not guessed
                           // from character containment.
let selId = null;          // blue selection = extend/remove target
let curSel = null;         // {start,end} current char-index selection
let linkFrom = null;       // when non-null we are in LINK MODE: node clicks
                           // STAGE a pending target (linkTo) rather than commit.
let linkTo = null;         // pending target id (staged, not yet confirmed). Lets
                           // you scroll/search for the right node; confirm commits.
// ── Lean mapping ───────────────────────────────────────────────────────────
// Each NL box MAY carry box.lean describing how it maps to the Lean source:
//   {file, start, end}  — a char span [start,end) into that .lean file's text
//   {none:true}         — explicitly mapped to nothing
//   (absent)            — not yet mapped
// plus optional ok:true|false (the faithful / not-faithful judgement). The Lean
// side mirrors the NL tree: the mapping hangs off each box, saved with the tree.
let LEAN_FILES = [];       // list of 'lean/…/X.lean' paths (from /lean-files)
let LEAN_FILE = null;      // path of the file currently shown in the Lean pane
let LEAN_TEXT = '';        // raw text of LEAN_FILE (char offsets index into this)
const LEAN_CACHE = {};     // path -> text
let leanCurSel = null;     // {file,start,end} current selection inside Lean pane
let dirty = false;
let idCounter = 1;
const freshId = () => 'b' + (idCounter++);
const COLLAPSED = {};

// ── LABELS ──────────────────────────────────────────────────────────────────
// Each box MAY carry box.label (a function/grammar label). The allowed label of
// a box is constrained by its PARENT box's label: valid children = the parent
// label's decomposition. See doc/labels.md. LABEL_CHILDREN[x] = labels allowed
// directly inside a box labelled x. A label absent here (or 'base' ones) admits
// no children. ROOT (unlabelled) uses LABEL_ROOT.
const LABEL_ROOT = ['commentary','definition','theorem','organizer-section'];
const LABEL_CHILDREN = {
  'organizer-section': ['commentary','definition','theorem','organizer-section'],
  'definition':        ['term','formula'],
  'theorem':           ['formula','proof'],
  'proof':             ['formula','commentary','theorem','tactic'],
  'formula':           ['external-citation','atomic-formula','compound-formula'],
  'atomic-formula':    ['relation','equality'],
  'relation':          ['relation-symbol','term'],
  'equality':          ['equality-symbol','term'],
  'compound-formula':  ['quantified','connective'],
  'quantified':        ['universal','existential'],
  'universal':         ['quantifier','variable-symbol','formula'],
  'existential':       ['quantifier','variable-symbol','formula'],
  'connective':        ['negation','implication','conjunction','disjunction'],
  'negation':          ['connective-symbol','formula'],
  'implication':       ['connective-symbol','formula'],
  'conjunction':       ['connective-symbol','formula'],
  'disjunction':       ['connective-symbol','formula'],
  'term':              ['external-citation','implicit-external-reference','atomic-term','composite-term'],
  'atomic-term':       ['variable','constant'],
  'variable':          ['variable-symbol'],
  'constant':          ['constant-symbol'],
  'composite-term':    ['function-application'],
  'function-application':['function-symbol','term'],
};
// labels valid for a box given its parent box (null parent → root set).
function allowedLabels(parentBox){ if(!parentBox||!parentBox.label) return LABEL_ROOT;
  return LABEL_CHILDREN[parentBox.label]||[]; }

const $ = (x) => document.getElementById(x);
function boxHue(id){const n=parseInt(String(id).replace(/\D/g,''),10)||0;return Math.round((n*137.508)%360);}
function boxColor(id){return `hsl(${boxHue(id)} 72% 50%)`;}
function hueRGB(id){const h=boxHue(id)/360,s=.72,l=.5;const f=(n)=>{const k=(n+h*12)%12;return l-s*Math.min(l,1-l)*Math.max(-1,Math.min(k-3,9-k,1));};return [f(0),f(8),f(4)];}
function rgbToHex(c){return '#'+c.map((v)=>Math.round(255*Math.max(0,Math.min(1,v))).toString(16).padStart(2,'0')).join('');}
function boxHex(id){return rgbToHex(hueRGB(id));}
function blendHex(ids){const a=[0,0,0];ids.forEach((id)=>{const c=hueRGB(id);a[0]+=c[0];a[1]+=c[1];a[2]+=c[2];});return rgbToHex(a.map((v)=>v/ids.length));}

/* ───────────────── tree helpers ───────────────── */
function walk(n,fn,d=0){fn(n,d);n.children.forEach((c)=>walk(c,fn,d+1));}
function find(id){let f=null;walk(ROOT,(n)=>{if(n.id===id)f=n;});return f;}
function parentOf(id){let p=null;walk(ROOT,(n)=>{if(n.children.some((c)=>c.id===id))p=n;});return p;}
function pieces(b){return b.pieces||[];}
function regionLen(b){return pieces(b).reduce((t,p)=>t+(p.end-p.start),0);}

/* ───────────────── link helpers ───────────────── */
function links(){ if(!ROOT.links) ROOT.links=[]; return ROOT.links; }
function addLink(from,to){ if(!from||!to||from===to) return false;
  if(links().some((l)=>l.from===from&&l.to===to)) return false;   // no dupes
  links().push({from,to}); markDirty(); return true; }
function removeLink(from,to){ ROOT.links=links().filter((l)=>!(l.from===from&&l.to===to)); markDirty(); }
function linksFrom(id){ return links().filter((l)=>l.from===id); }
function linksTo(id){ return links().filter((l)=>l.to===id); }
// enter/leave link mode (source already selected). target is STAGED then confirmed.
function startLink(){ const b=selId&&find(selId); if(!b){flash('select a source node first');return;} linkFrom=selId; linkTo=null; refreshAll(); flash('linking from “'+label(b)+'” → click a target, then confirm (Esc cancels)'); }
function cancelLink(){ if(linkFrom||linkTo){linkFrom=null;linkTo=null;refreshAll();} }
// clicking a node while armed STAGES it as the pending target (does not commit),
// so you can keep scrolling/searching and re-click a different node to restage.
function stageLink(toId){ if(!linkFrom) return false; if(toId===linkFrom){ linkTo=null; refreshAll(); flash("can't link a node to itself — pick a different target"); return true; }
  linkTo=toId; refreshAll(); return true; }
// confirm button / Enter: actually create the staged link.
function confirmLink(){ if(!linkFrom||!linkTo){flash('pick a target node first');return;}
  const ok=addLink(linkFrom,linkTo); const from=linkFrom, to=linkTo; linkFrom=null; linkTo=null;
  selId=from; flash(ok?'linked → “'+label(find(to))+'”':'that link already exists'); refreshAll(); }

/* ───────────────── Lean mapping ───────────────── */
// load the list of available .lean files, build a nested folder tree, render it
// in the "Lean files" tab, and show the main declaration file first.
async function initLean(){
  try{ LEAN_FILES=await fetch('/lean-files').then((r)=>r.ok?r.json():[]); }catch(_){ LEAN_FILES=[]; }
  renderLeanTree();
  // prefer the item's main declaration file for the first view, else first file
  const main=LEAN_FILES.find((f)=>/MaxSupportKernel\.lean$/.test(f))||LEAN_FILES[0];
  if(main) await showLeanFile(main);
}
// build a nested {name, path, children:[], isFile} tree from the flat path list.
// Robust to arbitrary folder depth; files with no folders just sit at the root.
function leanFileTree(){ const root={name:'',path:'',children:[],isFile:false};
  for(const full of LEAN_FILES){ const parts=full.split('/'); let node=root, acc='';
    parts.forEach((part,i)=>{ acc=acc?acc+'/'+part:part; const isFile=(i===parts.length-1);
      let child=node.children.find((c)=>c.name===part&&c.isFile===isFile);
      if(!child){ child={name:part,path:acc,children:[],isFile}; node.children.push(child); }
      node=child; }); }
  // sort each level: folders first, then files, alphabetically
  const sortRec=(n)=>{ n.children.sort((a,b)=> (a.isFile-b.isFile) || a.name.localeCompare(b.name)); n.children.forEach(sortRec); };
  sortRec(root); return root; }
const LEAN_FOLD={};   // folder path -> collapsed?
function renderLeanTree(){ const host=$('leanTree'); if(!host) return; host.innerHTML='';
  const root=leanFileTree();
  const addNodes=(parent,el,depth)=>{ parent.children.forEach((n)=>{
    const row=document.createElement('div'); row.className='row leanfrow'+(n.isFile&&n.path===LEAN_FILE?' picked':'');
    row.style.paddingLeft=(6+depth*13)+'px';
    if(n.isFile){
      const ic=document.createElement('span'); ic.className='twist leaf'; ic.textContent='·'; row.appendChild(ic);
      const nm=document.createElement('span'); nm.className='rname'; nm.textContent=n.name; row.appendChild(nm);
      row.onclick=()=>showLeanFile(n.path);
    } else {
      const collapsed=!!LEAN_FOLD[n.path];
      const tw=document.createElement('span'); tw.className='twist'; tw.textContent=collapsed?'▸':'▾'; row.appendChild(tw);
      const nm=document.createElement('span'); nm.className='rname folder'; nm.textContent=n.name+'/'; row.appendChild(nm);
      row.onclick=()=>{ LEAN_FOLD[n.path]=!collapsed; renderLeanTree(); };
    }
    el.appendChild(row);
    if(!n.isFile && !LEAN_FOLD[n.path]) addNodes(n,el,depth+1);
  }); };
  addNodes(root,host,0);
}
async function leanTextOf(path){ if(LEAN_CACHE[path]!=null) return LEAN_CACHE[path];
  const t=await fetch('../'+path).then((r)=>r.ok?r.text():''); LEAN_CACHE[path]=t; return t; }
// render one Lean file as selectable text; one span per line carrying its base
// char offset, so a DOM selection maps back to [start,end) into LEAN_TEXT.
async function showLeanFile(path){ if(!path) return; LEAN_FILE=path; LEAN_TEXT=await leanTextOf(path);
  const lbl=$('leanFileLabel'); if(lbl) lbl.textContent=path.replace(/^lean\//,'');
  renderLeanTree();   // refresh active-file highlight in the file tree
  const host=$('leanCode'); host.innerHTML=''; let off=0; const lines=LEAN_TEXT.split('\n');
  lines.forEach((ln,i)=>{ const row=document.createElement('div'); row.className='lean-line';
    const gut=document.createElement('span'); gut.className='lean-gut'; gut.textContent=i+1; row.appendChild(gut);
    const code=document.createElement('span'); code.className='lean-src'; code.dataset.start=off; code.textContent=ln.length?ln:'​';
    row.appendChild(code); host.appendChild(row); off+=ln.length+1; });  // +1 for the '\n'
  paintLeanHighlights();
}
// DOM selection in the Lean pane -> {file,start,end} into LEAN_TEXT.
function readLeanSelection(){ const s=window.getSelection(); if(!s||s.rangeCount===0||s.isCollapsed) return null;
  const r=s.getRangeAt(0); const aEl=leanSpanOf(r.startContainer), zEl=leanSpanOf(r.endContainer);
  if(!aEl||!zEl) return null;
  const a=+aEl.dataset.start+leanOff(r.startContainer,r.startOffset,aEl);
  const b=+zEl.dataset.start+leanOff(r.endContainer,r.endOffset,zEl);
  let lo=Math.min(a,b), hi=Math.max(a,b); if(lo>=hi) return null;
  return {file:LEAN_FILE,start:lo,end:hi}; }
function leanSpanOf(node){ let x=node.nodeType===3?node.parentElement:node; while(x&&!(x.dataset&&x.dataset.start!==undefined&&x.classList&&x.classList.contains('lean-src'))) x=x.parentElement; return x||null; }
function leanOff(node,off,span){ if(node.nodeType===3) return Math.min(off, span.textContent.replace('​','').length); return off===0?0:span.textContent.replace('​','').length; }

// set / clear / judge the selected box's Lean mapping
// A box's Lean mapping is a LIST of spans (possibly across several files), so
// one NL box can cite multiple Lean locations. Helpers read it uniformly.
function leanSpans(b){ return (b&&b.lean&&b.lean.spans)||[]; }
function leanIsNone(b){ return !!(b&&b.lean&&b.lean.none); }
// normalize legacy data: single-span mapping ({file,start,end}) -> list form,
// and the old boolean lean.ok -> the new box.verdict ('ok'|'notok') on leaves.
function normalizeLean(){ walk(ROOT,(n)=>{
  if(n.lean&&!n.lean.none&&!n.lean.spans&&n.lean.file!=null){ const {file,start,end}=n.lean; n.lean={spans:[{file,start,end}]}; }
  if(n.lean&&n.lean.ok!==undefined){ if(isLeaf(n)&&!n.verdict) n.verdict=n.lean.ok?'ok':'notok'; delete n.lean.ok; }
}); }

/* ───────── faithfulness verdict (ok / notok / undecidable) ───────── */
// Leaves are judged MANUALLY; parents are DERIVED from their descendants.
function isLeaf(n){ return !n.children||n.children.length===0; }
// a node's verdict: 'ok' | 'notok' | 'undecidable' | 'unset'.
//  leaf   → its stored n.verdict (unset if none)
//  parent → rollup: any notok ⇒ notok; else all ok ⇒ ok; else undecidable
//           (a parent only fails hard when a leaf genuinely fails; anything
//            unjudged/ambiguous leaves it undecidable, not falsely notok)
function verdictOf(n){ if(isLeaf(n)) return n.verdict||'unset';
  let anyNotok=false, allOk=true;
  for(const c of n.children){ const v=verdictOf(c); if(v==='notok')anyNotok=true; if(v!=='ok')allOk=false; }
  if(anyNotok) return 'notok'; if(allOk) return 'ok'; return 'undecidable'; }
// set/toggle a leaf's verdict. Clicking the active verdict again clears it.
function setVerdict(v){ const b=selId&&find(selId); if(!b){flash('select a box first');return;}
  if(!isLeaf(b)){flash('only leaf segments are judged — parents are derived from their children');return;}
  if(b.verdict===v) delete b.verdict; else b.verdict=v; markDirty(); refreshAll(); }
// set/clear the selected box's grammar label. '' clears. Enforced against the
// parent's allowed set (the <select> only offers valid options anyway).
function setLabel(v){ const b=selId&&find(selId); if(!b){flash('select a box first');return;}
  if(!v){ delete b.label; } else { if(!allowedLabels(parentOf(b.id)).includes(v)){flash('“'+v+'” not allowed under this parent');return;} b.label=v; }
  markDirty(); refreshAll(); }
// sort + merge overlapping/adjacent spans WITHIN the same file.
function mergeLeanSpans(b){ const sp=b.lean.spans; sp.sort((x,y)=> x.file<y.file?-1:x.file>y.file?1:x.start-y.start);
  const out=[]; for(const p of sp){ const last=out[out.length-1];
    if(last&&last.file===p.file&&p.start<=last.end){ last.end=Math.max(last.end,p.end); } else out.push({...p}); }
  b.lean.spans=out; }

// m: ADD the current Lean selection as another span of the selected box.
function mapLean(){ const b=selId&&find(selId); if(!b){flash('select an NL box first');return;}
  if(!leanCurSel){flash('select text in the Lean pane first');return;}
  if(!b.lean||b.lean.none) b.lean={spans:[]}; if(!b.lean.spans) b.lean.spans=[];
  b.lean.spans.push({file:leanCurSel.file,start:leanCurSel.start,end:leanCurSel.end}); mergeLeanSpans(b);
  markDirty(); window.getSelection().removeAllRanges(); leanCurSel=null;
  flash('added Lean span → “'+label(b)+'” ('+b.lean.spans.length+' total)'); refreshAll(); }
// r (in the Lean pane): SUBTRACT the current Lean selection from the box's spans
// — same splitting behavior as removeSel does for NL pieces.
function removeLeanSel(){ const b=selId&&find(selId); if(!b){flash('select an NL box first');return;}
  if(!leanCurSel){flash('select Lean text to remove first');return;}
  const spans=leanSpans(b); if(!spans.length){flash('this box has no Lean spans');return;}
  const {file,start:s,end:e}=leanCurSel; const next=[]; let changed=false;
  for(const p of spans){ if(p.file!==file||e<=p.start||s>=p.end){ next.push(p); continue; }
    changed=true; if(s>p.start) next.push({file:p.file,start:p.start,end:Math.min(s,p.end)});
    if(e<p.end) next.push({file:p.file,start:Math.max(e,p.start),end:p.end}); }
  if(!changed){flash('selection does not overlap a mapped Lean span');return;}
  if(next.length){ b.lean.spans=next; } else { delete b.lean; }
  markDirty(); window.getSelection().removeAllRanges(); leanCurSel=null; flash('removed Lean span from “'+label(b)+'”'); refreshAll(); }
// remove one span by index (tree ✕).
function removeLeanSpan(id,idx){ const b=find(id); if(!b||!b.lean||!b.lean.spans)return;
  b.lean.spans.splice(idx,1); if(!b.lean.spans.length) delete b.lean; markDirty(); refreshAll(); }
function mapLeanNone(){ const b=selId&&find(selId); if(!b){flash('select an NL box first');return;}
  b.lean={none:true}; markDirty(); flash('“'+label(b)+'” → mapped to nothing'); refreshAll(); }
function clearLean(){ const b=selId&&find(selId); if(!b)return; delete b.lean; markDirty(); refreshAll(); }

// jump the Lean pane to a box's FIRST mapped span and highlight it.
async function jumpToLean(b){ const spans=leanSpans(b); if(!spans.length) return; const first=spans[0];
  if(first.file!==LEAN_FILE) await showLeanFile(first.file);
  paintLeanHighlights();
  const el=[...$('leanCode').querySelectorAll('.lean-src')].reverse().find((s)=>+s.dataset.start<=first.start);
  if(el) el.scrollIntoView({block:'center',behavior:'smooth'}); }

// paint the Lean pane with the SAME focus view as the PDF: the current LEVEL
// node's mapped spans show grey (like the level outline), and its DIRECT
// CHILDREN's mapped spans show in their own colors. Spans outside the focus are
// not drawn — identical scoping to paintHighlights.
function paintLeanHighlights(){ const host=$('leanCode'); if(!host) return;
  host.querySelectorAll('.lean-hl').forEach((e)=>e.remove());
  const {level,self,children}=focusView();
  // 1) the level node itself: grey (skip at root = whole paper)
  if(self){ leanSpans(level).forEach((p)=>{ if(p.file===LEAN_FILE) paintLeanRange(p.start,p.end,null,{level:true}); }); }
  // 2) its direct children: each in its own color
  children.forEach((id)=>{ const n=find(id); leanSpans(n).forEach((p)=>{ if(p.file===LEAN_FILE)
    paintLeanRange(p.start,p.end,boxHex(id),{sel:id===selId}); }); }); }
// draw highlight boxes over the Lean char range [s,e) by wrapping affected line
// spans with absolutely-positioned overlays measured from Range rects.
// opts.level => grey see-through (the current level node); opts.sel => stronger
// fill + ring (the blue/own-color selected child); else normal child fill.
function paintLeanRange(s,e,color,opts){ opts=opts||{}; const host=$('leanCode');
  const srcs=[...host.querySelectorAll('.lean-src')];
  for(const code of srcs){ const base=+code.dataset.start; const tlen=code.textContent.replace('​','').length; const lineEnd=base+tlen;
    if(e<=base||s>=lineEnd+1) continue;                 // no overlap with this line (+1 for newline)
    const ls=Math.max(s,base)-base, le=Math.min(e,lineEnd)-base; if(le<ls) continue;
    const tn=code.firstChild; if(!tn||tn.nodeType!==3){ continue; }
    const rng=document.createRange();
    try{ rng.setStart(tn,Math.max(0,Math.min(ls,tn.length))); rng.setEnd(tn,Math.max(0,Math.min(le,tn.length))); }catch(_){ continue; }
    const rects=rng.getClientRects(); const hostBox=host.getBoundingClientRect();
    for(const rc of rects){ const d=document.createElement('div'); d.className='lean-hl'+(opts.sel?' sel':'');
      d.style.left=(rc.left-hostBox.left+host.scrollLeft)+'px'; d.style.top=(rc.top-hostBox.top+host.scrollTop)+'px';
      d.style.width=rc.width+'px'; d.style.height=rc.height+'px';
      if(opts.level){ d.style.background='rgba(120,120,120,0.10)'; }  // level: faint grey, see-through
      else { d.style.background=color+(opts.sel?'4d':'24'); }         // selected = stronger (soft) fill
      host.appendChild(d); } }
}

/* ───────────────── render PDF + build char sequence ───────────────── */
async function renderPdf(){
  const lib=window['pdfjs-dist/build/pdf']||window.pdfjsLib;
  lib.GlobalWorkerOptions.workerSrc='https://cdn.jsdelivr.net/npm/pdfjs-dist@3.11.174/build/pdf.worker.min.js';
  const pdf=await lib.getDocument('../paper.pdf').promise;
  const host=$('pages'); host.innerHTML=''; pageEls={}; CHARS=''; CHARMETA=[];
  // one SVG overlay spanning the whole pages stack, for drawing link arrows
  const svg=document.createElementNS('http://www.w3.org/2000/svg','svg');
  svg.id='arrowLayer'; svg.setAttribute('class','arrow-layer'); host.appendChild(svg);
  const dpr=window.devicePixelRatio||1;
  for(let p=1;p<=pdf.numPages;p++){
    const page=await pdf.getPage(p);
    const vp=page.getViewport({scale:PDF_SCALE});
    const wrap=document.createElement('div'); wrap.className='page-wrap';
    wrap.style.width=vp.width+'px'; wrap.style.height=vp.height+'px';
    const canvas=document.createElement('canvas');
    canvas.width=Math.floor(vp.width*dpr); canvas.height=Math.floor(vp.height*dpr);
    canvas.style.width=vp.width+'px'; canvas.style.height=vp.height+'px';
    const ctx=canvas.getContext('2d'); ctx.scale(dpr,dpr); wrap.appendChild(canvas);
    const hl=document.createElement('div'); hl.className='hl-layer'; wrap.appendChild(hl);
    const tl=document.createElement('div'); tl.className='textLayer'; wrap.appendChild(tl);
    host.appendChild(wrap); pageEls[p]={wrap,hl};
    await page.render({canvasContext:ctx,viewport:vp}).promise;
    await buildTextLayer(page,vp,tl,p);
  }
  render();
}

// Build the selectable text layer for one page AND append its glyphs to the
// global CHARS sequence with per-character rects.
async function buildTextLayer(page,vp,tl,pno){
  const tc=await page.getTextContent();
  for(const item of tc.items){
    const str=item.str;
    if(!str) { continue; }
    // transform of this text item -> position/size in viewport px
    const tr=window.pdfjsLib ? window.pdfjsLib.Util.transform(vp.transform,item.transform)
                             : (window['pdfjs-dist/build/pdf']).Util.transform(vp.transform,item.transform);
    const x=tr[4], y=tr[5];
    const fontH=Math.hypot(tr[2],tr[3]);        // glyph height in px
    const w=item.width*vp.scale;                 // total item width in px
    const h=fontH;
    // one span per item for selection; positioned like PDF.js does
    const span=document.createElement('span');
    span.textContent=str;
    span.style.left=x+'px';
    span.style.top=(y-fontH)+'px';
    span.style.fontSize=fontH+'px';
    span.style.fontFamily='sans-serif';
    // scale the span horizontally so its rendered width matches the PDF item
    span.dataset.start=CHARS.length;
    tl.appendChild(span);
    // after layout, scaleX to fit w (so transparent text aligns with glyphs)
    requestAnimationFrame(()=>{ const natural=span.getBoundingClientRect().width/ (span._sx||1);
      if(natural>0){ const sx=w/natural; span._sx=sx; span.style.transform=`scaleX(${sx})`; } });
    // per-character rects: distribute the item width evenly across its chars
    const n=str.length, cw=w/n;
    for(let k=0;k<n;k++){
      CHARMETA.push({page:pno, x:x+k*cw, y:y-fontH, w:cw, h:h});
    }
    CHARS+=str;
    span.dataset.end=CHARS.length;
    // add a single space between items on the same line? PDF.js hasEOL handles
    // line breaks; we add a newline char at item end if the item ends a line.
    if(item.hasEOL){ CHARMETA.push({page:pno,x:x+w,y:y-fontH,w:0,h:h}); CHARS+='\n'; }
  }
}

/* ───────────────── selection → char indices ───────────────── */
function readSelection(){
  const s=window.getSelection(); if(!s||s.rangeCount===0||s.isCollapsed) return null;
  const r=s.getRangeAt(0);
  const aSpan=spanOf(r.startContainer), zSpan=spanOf(r.endContainer);
  if(!aSpan||!zSpan) return null;
  const a=+aSpan.dataset.start + clampOff(r.startContainer,r.startOffset,aSpan);
  const b=+zSpan.dataset.start + clampOff(r.endContainer,r.endOffset,zSpan);
  let lo=Math.min(a,b), hi=Math.max(a,b);
  if(lo>=hi) return null;
  return {start:lo,end:hi};
}
// a PDF text-layer span only (NOT a Lean code span, which also carries
// dataset.start) — so PDF and Lean selections never cross-contaminate.
function spanOf(node){ let x=node.nodeType===3?node.parentElement:node; while(x&&!(x.dataset&&x.dataset.start!==undefined&&x.parentElement&&x.parentElement.classList.contains('textLayer'))) x=x.parentElement; return x||null; }

// a box AT the current level (i.e. a direct child of levelId) whose region
// covers character index `i`. Click-select is scoped to the level you're in:
// at top level you pick top-level boxes, inside a level you pick its children —
// never a deeper leaf. Innermost among the eligible children wins.
function boxAtChar(i){
  const kids=(find(levelId)||ROOT).children;
  let best=null,bw=Infinity;
  kids.forEach((n)=>{ if(pieces(n).some((p)=>p.start<=i&&i<p.end)){ const w=regionLen(n); if(w<bw){bw=w;best=n;} } });
  return best;
}
// innermost node ANYWHERE in the tree whose region covers char i (for link
// targeting, which is not scoped to the current level).
function boxAtCharGlobal(i){ let best=null,bw=Infinity; walk(ROOT,(n)=>{ if(n===ROOT)return;
  if(pieces(n).some((p)=>p.start<=i&&i<p.end)){ const w=regionLen(n); if(w<bw){bw=w;best=n;} } }); return best; }
// select a box (blue) + reveal it in the tree (expand ancestors, scroll to row)
function selectBox(id){ selId=id; let p=parentOf(id); while(p){COLLAPSED[p.id]=false;p=parentOf(p.id);} render();
  const r=[...$('tree').querySelectorAll('.row')].find((x)=>x._id===id); if(r) r.scrollIntoView({block:'nearest'});
  const b=find(id); if(b&&b.lean&&!b.lean.none) jumpToLean(b); }
// plain left-click on the PDF (no text selected) over a box -> select that box
function onPdfClick(e){
  if(window.getSelection && !window.getSelection().isCollapsed) return;   // a drag-select -> leave it
  const sp=spanOf(e.target); if(!sp) return;
  // char index at the click: start of the span + offset into its text by x
  let i=+sp.dataset.start;
  // refine within the span using caretRangeFromPoint if available
  const cr=document.caretRangeFromPoint?document.caretRangeFromPoint(e.clientX,e.clientY):null;
  if(cr && cr.startContainer && spanOf(cr.startContainer)===sp) i=+sp.dataset.start+clampOff(cr.startContainer,cr.startOffset,sp);
  if(linkFrom){ const tgt=boxAtCharGlobal(i); if(tgt) stageLink(tgt.id); return; }  // link: stage target (any node)
  const box=boxAtChar(i); if(box) selectBox(box.id);
}
// char index under a PDF pointer event (shared by click + dblclick).
function charAtPdfEvent(e){ const sp=spanOf(e.target); if(!sp) return null; let i=+sp.dataset.start;
  const cr=document.caretRangeFromPoint?document.caretRangeFromPoint(e.clientX,e.clientY):null;
  if(cr && cr.startContainer && spanOf(cr.startContainer)===sp) i=+sp.dataset.start+clampOff(cr.startContainer,cr.startOffset,sp);
  return i; }
// double-click on the PDF over a box -> enter it as the current level (mirrors
// double-click on a tree row).
function onPdfDblClick(e){ const i=charAtPdfEvent(e); if(i==null) return;
  const box=boxAtChar(i); if(box) enterLevel(box.id); }
function clampOff(node,off,span){ if(node.nodeType===3) return Math.min(off, span.textContent.length); return off===0?0:span.textContent.length; }

/* ───────────────── box ops ───────────────── */
async function makeBox(){
  if(!curSel) return;
  // The new node is added as a CHILD OF THE CURRENT NODE (levelId) — explicit
  // tree authoring. Three boxes over the same text are unambiguous: each lands
  // wherever you currently are in the tree, not inferred from overlap.
  const parent=find(levelId)||ROOT;
  const box={id:freshId(),pieces:[{start:curSel.start,end:curSel.end}],children:[]};
  parent.children.push(box); sortKids(parent);
  selId=box.id; markDirty(); clearSel(); refreshAll();
}
// enter a node: it becomes the current level (new boxes nest under it).
function enterLevel(id){ levelId=id; refreshAll(); }
// go up to the current node's parent.
function upLevel(){ if(levelId==='root')return; const p=parentOf(levelId); levelId=p?p.id:'root'; refreshAll(); }
function extendBox(){
  if(!curSel) return; const box=selId&&find(selId); if(!box){flash('select a box first');return;}
  box.pieces.push({start:curSel.start,end:curSel.end}); mergePieces(box);
  markDirty(); clearSel(); refreshAll();
}
function removeSel(){
  if(!curSel) return; const box=selId&&find(selId); if(!box){flash('select a box first');return;}
  const {start:s,end:e}=curSel; const next=[]; let changed=false;
  for(const p of pieces(box)){
    if(e<=p.start||s>=p.end){ next.push(p); continue; }
    changed=true;
    if(s>p.start) next.push({start:p.start,end:Math.min(s,p.end)});
    if(e<p.end) next.push({start:Math.max(e,p.start),end:p.end});
  }
  if(!changed){flash('selection does not overlap the selected box');return;}
  box.pieces=next; clearSel();
  if(!box.pieces.length){ deleteBox(box.id); return; }
  markDirty(); refreshAll();
}
function pieceContains(b,s,e){ return pieces(b).some((p)=>p.start<=s&&e<=p.end); }
function mergePieces(b){ b.pieces.sort((x,y)=>x.start-y.start); const out=[]; for(const p of b.pieces){ const last=out[out.length-1]; if(last&&p.start<=last.end) last.end=Math.max(last.end,p.end); else out.push({...p}); } b.pieces=out; }
function regionStart(b){ const ps=pieces(b); return ps.length?Math.min(...ps.map((p)=>p.start)):0; }
function sortKids(n){ n.children.sort((a,b)=>regionStart(a)-regionStart(b)); }
function deleteBox(id){ const p=parentOf(id); if(!p) return; const i=p.children.findIndex((c)=>c.id===id); const rm=p.children[i]; p.children.splice(i,1,...rm.children); sortKids(p);
  ROOT.links=links().filter((l)=>l.from!==id&&l.to!==id);   // drop any links touching the deleted node
  if(selId===id)selId=null; if(levelId===id)levelId=p.id; if(linkFrom===id)linkFrom=null; if(linkTo===id)linkTo=null; markDirty(); refreshAll(); }
function removePiece(id,idx){ const n=find(id); if(!n)return; n.pieces.splice(idx,1); if(!n.pieces.length){deleteBox(id);return;} markDirty(); refreshAll(); }

/* ───────────────── link arrows on the PDF ───────────────── */
// anchor box of a node in PAGES coordinates (px within the #pages stack):
// the bounding box of its FIRST piece's rects. Returns null if offscreen/unbuilt.
function anchorRect(id){ const b=find(id); if(!b) return null; const ps=pieces(b); if(!ps.length) return null;
  const p=ps[0]; let r=null;
  for(let i=p.start;i<p.end;i++){ const m=CHARMETA[i]; if(!m) continue; const pg=pageEls[m.page]; if(!pg) continue;
    const ox=pg.wrap.offsetLeft, oy=pg.wrap.offsetTop; const x0=ox+m.x,y0=oy+m.y,x1=x0+m.w,y1=y0+m.h;
    if(!r) r={x0,y0,x1,y1}; else { r.x0=Math.min(r.x0,x0); r.y0=Math.min(r.y0,y0); r.x1=Math.max(r.x1,x1); r.y1=Math.max(r.y1,y1); } }
  return r; }
function drawArrows(){ const svg=$('arrowLayer'); if(!svg) return; const host=$('pages');
  svg.setAttribute('width',host.scrollWidth); svg.setAttribute('height',host.scrollHeight);
  svg.innerHTML='';
  const NS='http://www.w3.org/2000/svg';
  // arrowhead marker (one per color would be heavy; use a single neutral head
  // we recolor via context-stroke fallback → just draw a small triangle path).
  const hi=selId;   // when a node is selected, its own arrows are emphasized
  // draw only links whose tail is a painted block at this level (shownLinks);
  // their dependents are faint-highlighted by paintHighlights, so both ends have
  // something on screen for the arrow to connect.
  shownLinks().forEach((l,idx)=>{
    const a=anchorRect(l.from), b=anchorRect(l.to); if(!a||!b) return;
    // connect from the right/left edge midpoints, whichever gives a cleaner curve
    const ay=(a.y0+a.y1)/2, by=(b.y0+b.y1)/2;
    // choose source/target x by relative position so the arrow reads naturally
    let sx,sy,tx,ty;
    if(b.x0 > a.x1){ sx=a.x1; tx=b.x0; } else if(b.x1 < a.x0){ sx=a.x0; tx=b.x1; } else { sx=(a.x0+a.x1)/2; tx=(b.x0+b.x1)/2; }
    sy=ay; ty=by;
    const col=boxHex(l.from); const emph=(hi===l.from||hi===l.to);
    // control points: bow the curve outward horizontally
    const dx=Math.max(40,Math.abs(tx-sx)*0.5), dir=tx>=sx?1:-1;
    const c1x=sx+dir*dx, c1y=sy, c2x=tx-dir*dx, c2y=ty;
    const path=document.createElementNS(NS,'path');
    path.setAttribute('d',`M ${sx} ${sy} C ${c1x} ${c1y} ${c2x} ${c2y} ${tx} ${ty}`);
    path.setAttribute('fill','none'); path.setAttribute('stroke',col);
    path.setAttribute('stroke-width',emph?2.5:1.5); path.setAttribute('opacity',emph?0.95:0.5);
    svg.appendChild(path);
    // arrowhead at target, oriented along the incoming tangent (c2 → t)
    const ang=Math.atan2(ty-c2y,tx-c2x), hlen=9, spread=0.42;
    const h1x=tx-hlen*Math.cos(ang-spread), h1y=ty-hlen*Math.sin(ang-spread);
    const h2x=tx-hlen*Math.cos(ang+spread), h2y=ty-hlen*Math.sin(ang+spread);
    const head=document.createElementNS(NS,'path');
    head.setAttribute('d',`M ${tx} ${ty} L ${h1x} ${h1y} L ${h2x} ${h2y} Z`);
    head.setAttribute('fill',col); head.setAttribute('opacity',emph?0.95:0.5);
    svg.appendChild(head);
  });
  // link mode preview: dashed ring on the source, and — once a target is staged
  // — a dashed preview arrow source → staged target (not yet committed).
  if(linkFrom){ const a=anchorRect(linkFrom); const col=boxHex(linkFrom);
    if(a){ const ring=document.createElementNS(NS,'rect');
      ring.setAttribute('x',a.x0-3); ring.setAttribute('y',a.y0-3); ring.setAttribute('width',a.x1-a.x0+6); ring.setAttribute('height',a.y1-a.y0+6);
      ring.setAttribute('fill','none'); ring.setAttribute('stroke',col); ring.setAttribute('stroke-width',2); ring.setAttribute('stroke-dasharray','5 4'); ring.setAttribute('rx',3);
      svg.appendChild(ring); }
    const t=linkTo&&anchorRect(linkTo);
    if(a&&t){ // ring the staged target too
      const tr=document.createElementNS(NS,'rect');
      tr.setAttribute('x',t.x0-3); tr.setAttribute('y',t.y0-3); tr.setAttribute('width',t.x1-t.x0+6); tr.setAttribute('height',t.y1-t.y0+6);
      tr.setAttribute('fill','none'); tr.setAttribute('stroke',col); tr.setAttribute('stroke-width',2); tr.setAttribute('stroke-dasharray','5 4'); tr.setAttribute('rx',3);
      svg.appendChild(tr);
      // dashed preview curve a → staged target, with arrowhead
      let sx,sy,tx,ty; const ay=(a.y0+a.y1)/2, by=(t.y0+t.y1)/2;
      if(t.x0>a.x1){ sx=a.x1; tx=t.x0; } else if(t.x1<a.x0){ sx=a.x0; tx=t.x1; } else { sx=(a.x0+a.x1)/2; tx=(t.x0+t.x1)/2; }
      sy=ay; ty=by; const dx=Math.max(40,Math.abs(tx-sx)*0.5), dir=tx>=sx?1:-1;
      const c1x=sx+dir*dx, c2x=tx-dir*dx;
      const path=document.createElementNS(NS,'path');
      path.setAttribute('d',`M ${sx} ${sy} C ${c1x} ${sy} ${c2x} ${ty} ${tx} ${ty}`);
      path.setAttribute('fill','none'); path.setAttribute('stroke',col); path.setAttribute('stroke-width',2.5); path.setAttribute('stroke-dasharray','6 4'); path.setAttribute('opacity',0.9);
      svg.appendChild(path);
      const aa=Math.atan2(ty-ty, tx-c2x), hlen=9, spread=0.42;   // tangent c2→end (horizontal)
      const h1x=tx-hlen*Math.cos(aa-spread), h1y=ty-hlen*Math.sin(aa-spread);
      const h2x=tx-hlen*Math.cos(aa+spread), h2y=ty-hlen*Math.sin(aa+spread);
      const head=document.createElementNS(NS,'path');
      head.setAttribute('d',`M ${tx} ${ty} L ${h1x} ${h1y} L ${h2x} ${h2y} Z`); head.setAttribute('fill',col); head.setAttribute('opacity',0.9);
      svg.appendChild(head);
    }
  }
}

/* ───────────────── paint highlights on the PDF ───────────────── */
function render(){ paintHighlights(); drawArrows(); renderTree(); updateSelUI(); paintLeanHighlights(); }

// SINGLE SOURCE OF TRUTH for the focus view at the current level.
//  - `level`    : the current level node (outline; ROOT = whole paper)
//  - `children` : its direct children (the blocks painted filled)
//  - `painted`  : the set of blocks shown on screen = the level node (outline) +
//    its direct children (filled). Link visibility keys off this set.
function focusView(){ const level=find(levelId)||ROOT;
  const self = level!==ROOT ? level.id : null;
  const children = level.children.map((c)=>c.id);
  const painted = new Set(children); if(self) painted.add(self);
  return {level, self, children, painted}; }

// A link's arrow is drawn when its TAIL (from) is a painted block at this level
// and we are not at the top level. Showing a link reveals its DEPENDENT (to),
// which gets faint-highlighted (see paintHighlights) so the arrow has a visible
// destination even when the target isn't itself a block at this level.
function shownLinks(){ const {level,painted}=focusView(); if(level===ROOT) return [];
  return links().filter((l)=>painted.has(l.from)); }

function paintHighlights(){
  for(const p of Object.values(pageEls)) p.hl.innerHTML='';
  const {level}=focusView();
  // 0) dependents of shown links: the TARGET block of each visible link, painted
  // first (underneath) in a faint tint so it reads as "revealed by a link", not a
  // normal block and not the blue selection. Colored by the link's tail.
  shownLinks().forEach((l)=>{ const t=find(l.to); if(!t) return;
    pieces(t).forEach((p)=>drawRange(p.start,p.end,boxHex(l.from),{dep:true})); });
  // 1) the level box itself: outline only (skip for root = whole paper)
  if(level!==ROOT){ pieces(level).forEach((p)=>drawRange(p.start,p.end,boxHex(level.id),{outline:true})); }
  // 2) its direct children: filled (blended where children overlap)
  const kids=level.children;
  const ranges=[]; kids.forEach((n)=>pieces(n).forEach((p)=>ranges.push({start:p.start,end:p.end,id:n.id})));
  if(ranges.length){
    const pts=new Set(); ranges.forEach((r)=>{pts.add(r.start);pts.add(r.end);});
    const sorted=[...pts].sort((a,b)=>a-b);
    for(let k=0;k<sorted.length-1;k++){
      const s=sorted[k],e=sorted[k+1];
      const cover=ranges.filter((r)=>r.start<=s&&e<=r.end);
      if(!cover.length) continue;
      drawRange(s,e,blendHex(cover.map((r)=>r.id)),{sel: selId&&cover.some((r)=>r.id===selId)});
    }
  }
}
// draw highlight rects for char range [s,e). Fills are kept LIGHT so glyphs
// (esp. math) stay readable under overlaps; selection is shown with a soft
// dashed outline (drawn at edges only, never a solid border over the text).
// opts.outline => current level (grey, see-through); opts.sel => selected child;
// opts.dep => link-dependent reveal.
function drawRange(s,e,color,opts){
  opts=opts||{}; let run=null;
  const flush=()=>{ if(!run)return; const pg=pageEls[run.page]; if(pg){ const d=document.createElement('div');
    // selected => feathered/soft (.hl.sel has blur); others => crisp hard edge
    d.className='hl'+(opts.sel?' sel':'');
    d.style.left=run.x0+'px'; d.style.top=run.y0+'px';
    d.style.width=(run.x1-run.x0)+'px'; d.style.height=(run.y1-run.y0)+'px';
    if(opts.outline){ d.style.background='rgba(120,120,120,0.09)'; }  // current level: faint grey, see-through
    else if(opts.dep){ d.style.background=color+'22'; }              // link dependent: faint tint
    else { d.style.background=color+(opts.sel?'4d':'24'); }          // selected = stronger (soft) fill
    pg.hl.appendChild(d);} run=null; };
  for(let i=s;i<e;i++){ const m=CHARMETA[i]; if(!m){flush();continue;}
    if(run && m.page===run.page && Math.abs(m.y-run.y0)<3){ run.x1=Math.max(run.x1,m.x+m.w); run.y1=Math.max(run.y1,m.y+m.h); }
    else { flush(); run={page:m.page,x0:m.x,y0:m.y,x1:m.x+m.w,y1:m.y+m.h}; } }
  flush();
}

/* ───────────────── tree panel ───────────────── */
function renderTree(){
  const host=$('tree'); host.innerHTML=''; host.appendChild(treeRow(ROOT,true));
  // up buttons (labelbar + PDF header); shown only when not at top level
  const atRoot=levelId==='root';
  const up=$('upLevel'); if(up) up.style.display = atRoot?'none':'';
  const upP=$('upLevelPdf'); if(upP) upP.style.display = atRoot?'none':'';
}
function label(b){ if(!b) return '(none)'; const ps=pieces(b); if(!ps.length) return '(span)'; const t=CHARS.slice(ps[0].start,ps[0].end).replace(/\s+/g,' ').trim(); return (t.slice(0,30)||'(span)')+(ps.length>1?` …+${ps.length-1}`:''); }
function treeRow(node,isRoot){
  const wrap=document.createElement('div'); const row=document.createElement('div'); row._id=node.id;
  // anything to expand: child boxes OR multiple pieces -> this node folds
  const expandable = node.children.length>0 || pieces(node).length>1;
  const kids=node.children.length>0, collapsed=!!COLLAPSED[node.id];
  row.className='row'+(node.id===selId?' picked':'')+(node.id===levelId?' level':'');
  const tw=document.createElement('span'); tw.className='twist'+(expandable?'':' leaf'); tw.textContent=expandable?(collapsed?'▸':'▾'):'·';
  if(expandable) tw.onclick=(e)=>{e.stopPropagation();COLLAPSED[node.id]=!collapsed;renderTree();};
  row.appendChild(tw);
  if(!isRoot){const sw=document.createElement('span');sw.className='rswatch';sw.style.background=boxColor(node.id);row.appendChild(sw);}
  const nm=document.createElement('span'); nm.className='rname'; nm.textContent=isRoot?'paper':label(node); row.appendChild(nm);
  // label tag: small text chip of the box's grammar/function label
  if(!isRoot && node.label){ const lt=document.createElement('span'); lt.className='labeltag'; lt.textContent=node.label; lt.title='label: '+node.label; row.appendChild(lt); }
  // link badge: ➜n outgoing / ⬅n incoming (shown compact on the row itself)
  if(!isRoot){ const out=linksFrom(node.id).length, inc=linksTo(node.id).length;
    if(out||inc){ const lb=document.createElement('span'); lb.className='linkbadge';
      lb.textContent=(out?'➜'+out:'')+(out&&inc?' ':'')+(inc?'⬅'+inc:''); lb.title='links'; row.appendChild(lb); } }
  // Lean badge: λ (mapped, with count) or ∅ (none). Its COLOR carries the
  // verdict — green=ok, red=not ok, grey=undecidable/unjudged. Leaves are solid,
  // derived parents are outlined. Nothing shows on unmapped boxes.
  if(!isRoot && node.lean){ const lb=document.createElement('span');
    const v=verdictOf(node);
    lb.className='leanbadge '+v+(isLeaf(node)?' leafv':' derived');
    const nsp=leanSpans(node).length;
    lb.textContent=node.lean.none?'∅':('λ'+(nsp>1?nsp:''));
    const vtxt=v==='ok'?'faithful':v==='notok'?'not faithful':'undecidable';
    lb.title=(node.lean.none?'mapped to nothing':(nsp+' Lean span'+(nsp>1?'s':'')+': '+[...new Set(leanSpans(node).map((p)=>p.file.replace(/^lean\//,'')))].join(', ')))+' · '+(isLeaf(node)?'':'derived — ')+vtxt;
    row.appendChild(lb); }
  // (to make this node the current level for nesting, double-click the row)
  if(!isRoot){const del=document.createElement('span');del.className='rdel';del.textContent='✕';del.onclick=(e)=>{e.stopPropagation();deleteBox(node.id);};row.appendChild(del);}
  // single click: select (blue). double click: enter level.
  // while in LINK MODE, a click picks this node as the arrow target instead.
  row.onclick=()=>{ if(isRoot) return;
    if(linkFrom){ stageLink(node.id); return; }
    selId=node.id; render(); scrollToChar(pieces(node)[0].start);
    if(node.lean&&!node.lean.none) jumpToLean(node); };
  row.ondblclick=()=>{ enterLevel(node.id); };
  wrap.appendChild(row);
  // piece sub-rows (navigable) when >1 piece
  if(!isRoot && pieces(node).length>1 && !collapsed){
    const pb=document.createElement('div'); pb.className='children';
    pieces(node).forEach((p,pi)=>{ const pr=document.createElement('div'); pr.className='row piecerow';
      const pad=document.createElement('span');pad.className='twist leaf';pad.textContent='◦';pr.appendChild(pad);
      // pieces use a hollow diamond marker (not a filled box swatch) to read as
      // "a fragment of this box", visually distinct from a real child box.
      const dot=document.createElement('span');dot.className='pcmark';dot.style.color=boxColor(node.id);dot.textContent='◇';pr.appendChild(dot);
      const t=document.createElement('span');t.className='rname';t.textContent=`piece ${pi+1}: ${CHARS.slice(p.start,p.end).replace(/\s+/g,' ').trim().slice(0,20)||'(span)'}`;pr.appendChild(t);
      const del=document.createElement('span');del.className='rdel';del.textContent='✕';del.title='remove this piece';del.onclick=(e)=>{e.stopPropagation();removePiece(node.id,pi);};pr.appendChild(del);
      pr.onclick=()=>{selId=node.id;render();scrollToChar(p.start);}; pb.appendChild(pr); });
    wrap.appendChild(pb);
  }
  // link sub-rows: outgoing (➜ target) then incoming (⬅ source), each jumps to
  // the other node and can be deleted. Shown when the node is not collapsed.
  if(!isRoot && !collapsed){ const ls=[...linksFrom(node.id).map((l)=>({l,dir:'out',other:l.to})),
                                        ...linksTo(node.id).map((l)=>({l,dir:'in',other:l.from}))];
    if(ls.length){ const lbx=document.createElement('div'); lbx.className='children';
      ls.forEach(({l,dir,other})=>{ const lr=document.createElement('div'); lr.className='row linkrow'+(dir==='in'?' incoming':'');
        const pad=document.createElement('span');pad.className='twist leaf';pad.textContent=dir==='out'?'➜':'⬅';pad.style.opacity='.9';lr.appendChild(pad);
        const sw=document.createElement('span');sw.className='rswatch';sw.style.background=boxColor(l.from);lr.appendChild(sw);
        const t=document.createElement('span');t.className='rname';t.textContent=(dir==='out'?'to ':'from ')+label(find(other));lr.appendChild(t);
        const del=document.createElement('span');del.className='rdel';del.textContent='✕';del.title='delete link';del.onclick=(e)=>{e.stopPropagation();removeLink(l.from,l.to);refreshAll();};lr.appendChild(del);
        lr.onclick=()=>{ selId=other; render(); const o=find(other); if(o&&pieces(o).length)scrollToChar(pieces(o)[0].start); }; lbx.appendChild(lr); });
      wrap.appendChild(lbx); } }
  // Lean span sub-rows: one per mapped span (λ marker), click jumps the Lean
  // pane to it, ✕ removes just that span. Shown when the node is not collapsed.
  if(!isRoot && !collapsed){ const sp=leanSpans(node);
    if(sp.length){ const lbx=document.createElement('div'); lbx.className='children';
      sp.forEach((p,si)=>{ const lr=document.createElement('div'); lr.className='row leanrow';
        const pad=document.createElement('span');pad.className='twist leaf';pad.textContent='λ';pad.style.opacity='.9';lr.appendChild(pad);
        const t=document.createElement('span');t.className='rname';t.textContent=p.file.replace(/^lean\//,'')+` [${p.start}–${p.end}]`;lr.appendChild(t);
        const del=document.createElement('span');del.className='rdel';del.textContent='✕';del.title='remove this Lean span';del.onclick=(e)=>{e.stopPropagation();removeLeanSpan(node.id,si);};lr.appendChild(del);
        lr.onclick=async()=>{ selId=node.id; render(); await showLeanFile(p.file); paintLeanHighlights();
          const el=[...$('leanCode').querySelectorAll('.lean-src')].reverse().find((s)=>+s.dataset.start<=p.start); if(el) el.scrollIntoView({block:'center',behavior:'smooth'}); };
        lbx.appendChild(lr); });
      wrap.appendChild(lbx); } }
  if(kids && !collapsed){const box=document.createElement('div');box.className='children';node.children.forEach((c)=>box.appendChild(treeRow(c,false)));wrap.appendChild(box);}
  return wrap;
}
function scrollToChar(i){ const m=CHARMETA[i]; if(!m)return; const pg=pageEls[m.page]; if(!pg)return; $('pdfScroll').scrollTo({top:Math.max(0,pg.wrap.offsetTop+m.y-80),behavior:'smooth'}); }

/* ───────────────── ui glue ───────────────── */
function updateSelUI(){
  const mk=$('mkbox'),ex=$('extendbox'),rm=$('removebox'),lk=$('linkbox'),ck=$('confirmlink'),info=$('selinfo');
  const box=selId&&find(selId);
  // link button: idle → "link"; armed → "cancel". A separate confirm button
  // appears while armed and is only enabled once a target is staged.
  if(lk){ lk.disabled=!selId&&!linkFrom; lk.classList.toggle('armed',!!linkFrom);
    lk.innerHTML=linkFrom?'✕ cancel <kbd>Esc</kbd>':'&#10137; link <kbd>l</kbd>'; }
  if(ck){ ck.style.display=linkFrom?'':'none'; ck.disabled=!linkTo;
    ck.innerHTML=linkTo?('✓ confirm → “'+label(find(linkTo))+'” <kbd>↵</kbd>'):'✓ confirm (pick a target)'; }
  if(linkFrom){ info.textContent=linkTo
      ? `link “${label(find(linkFrom))}” → “${label(find(linkTo))}” · ↵ confirm · click another to change · Esc cancel`
      : `linking from “${label(find(linkFrom))}” · click/scroll to a target node · Esc cancel`;
    mk.disabled=true; ex.disabled=true; rm.disabled=true; return; }
  if(curSel){ mk.disabled=false; ex.disabled=!box;
    const overlaps=box&&pieces(box).some((p)=>curSel.start<p.end&&curSel.end>p.start); rm.disabled=!overlaps;
    const lvl=levelId==='root'?'paper':label(find(levelId));
    info.textContent=`“${CHARS.slice(curSel.start,curSel.end).replace(/\s+/g,' ').trim().slice(0,24)}” · n=new under ${lvl}`+(box?` · e=add to “${label(box)}”`:'');
  } else { mk.disabled=true; ex.disabled=true; rm.disabled=true; info.textContent=selId?`selected “${label(box)}” · l=link from here · m=map to Lean`:''; }
  updateLeanUI(); updateLabelUI();
}
// Label dropdown: offers only labels valid under the selected box's PARENT.
function updateLabelUI(){ const sel=$('labelSel'); if(!sel) return; const box=selId&&find(selId);
  if(!box){ sel.disabled=true; sel.innerHTML='<option value="">(none)</option>'; return; }
  sel.disabled=false;
  const opts=allowedLabels(parentOf(box.id));
  let html='<option value="">(none)</option>'+opts.map((o)=>`<option value="${o}">${o}</option>`).join('');
  // if the stored label is no longer valid under the parent, still show it (flagged)
  if(box.label && !opts.includes(box.label)) html+=`<option value="${box.label}">${box.label} (invalid here)</option>`;
  sel.innerHTML=html; sel.value=box.label||'';
}
// Lean toolbar: add (m), remove (r), none, clear + the verdict buttons.
function updateLeanUI(){ const box=selId&&find(selId);
  const map=$('leanMap'),unmap=$('leanUnmap'),none=$('leanNone'),clr=$('leanClear'),info=$('leanInfo');
  const ok=$('vOk'),notok=$('vNotok'),undec=$('vUndec');
  if(!map) return;
  const spans=leanSpans(box);
  // does the current Lean selection overlap an existing span of this box?
  const overlaps=box&&leanCurSel&&spans.some((p)=>p.file===leanCurSel.file&&leanCurSel.start<p.end&&leanCurSel.end>p.start);
  map.disabled=!box||!leanCurSel; if(unmap) unmap.disabled=!overlaps;
  none.disabled=!box; clr.disabled=!box||!box.lean;
  // verdict buttons: only LEAVES are judged manually; parents are derived.
  const leaf=box&&isLeaf(box); const cur=box?verdictOf(box):'unset';
  [ok,notok,undec].forEach((btn)=>{ if(btn) btn.disabled=!leaf; });
  if(ok){ ok.classList.toggle('on',leaf&&cur==='ok'); }
  if(notok){ notok.classList.toggle('on',leaf&&cur==='notok'); }
  if(undec){ undec.classList.toggle('on',leaf&&cur==='undecidable'); }
  if(!info) return;
  if(!box){ info.textContent='select an NL box to map it to Lean'; return; }
  const vtag=leaf?'':` · verdict (derived): ${verdictOf(box)}`;
  if(leanCurSel){ info.textContent=(overlaps?'r → remove · ':'m → add span · ')+`“${LEAN_TEXT.slice(leanCurSel.start,leanCurSel.end).replace(/\s+/g,' ').trim().slice(0,30)}”`; }
  else if(box.lean&&box.lean.none){ info.textContent=`“${label(box)}” → ∅ (nothing)`+vtag; }
  else if(spans.length){ info.textContent=`“${label(box)}” → ${spans.length} span${spans.length>1?'s':''}: `+spans.map((p)=>p.file.replace(/^lean\//,'')+` [${p.start}–${p.end}]`).join(', ')+vtag; }
  else { info.textContent=`“${label(box)}” — not mapped · select Lean text + m, or ∅ none`+vtag; }
}
function clearSel(){ window.getSelection().removeAllRanges(); curSel=null; }
function flash(m){ $('status').textContent=m; setTimeout(()=>{if($('status').textContent===m)$('status').textContent='';},3000); }
function refreshAll(){ paintHighlights(); drawArrows(); renderTree(); updateSelUI(); paintLeanHighlights(); }

/* ───────────────── save ───────────────── */
let _t=null; function markDirty(){dirty=true;clearTimeout(_t);_t=setTimeout(save,600);}
async function save(manual){ try{ const r=await fetch('/save',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(ROOT)});
  if(!r.ok)throw new Error('HTTP '+r.status); dirty=false; $('status').textContent=manual===true?'saved ✓':'autosaved'; setTimeout(()=>{if(!dirty)$('status').textContent='';},900);
}catch(e){flash('save failed: '+e.message);} }

/* ───────────────── splitter ───────────────── */
function setupSplitters(){ document.querySelectorAll('.splitter').forEach((sp)=>{ const left=$(sp.dataset.left);
  sp.addEventListener('pointerdown',(e)=>{e.preventDefault();sp.setPointerCapture(e.pointerId);sp.classList.add('drag');document.body.classList.add('resizing');
    const sx=e.clientX,sw=left.getBoundingClientRect().width;
    const mv=(ev)=>{left.style.flex='0 0 '+Math.max(160,sw+(ev.clientX-sx))+'px';};
    const up=(ev)=>{sp.releasePointerCapture(ev.pointerId);sp.classList.remove('drag');document.body.classList.remove('resizing');sp.removeEventListener('pointermove',mv);sp.removeEventListener('pointerup',up);};
    sp.addEventListener('pointermove',mv);sp.addEventListener('pointerup',up);}); }); }

// switch the left panel between the Boxes tree and the Lean file tree.
function switchTab(which){ const boxes=which==='boxes';
  $('viewBoxes').style.display=boxes?'':'none'; $('viewLean').style.display=boxes?'none':'';
  $('tabBoxes').classList.toggle('active',boxes); $('tabLean').classList.toggle('active',!boxes);
  if(!boxes) renderLeanTree(); }

/* ───────────────── init ───────────────── */
async function init(){
  try{ const t=await fetch('../tree.json').then((r)=>r.ok?r.json():null); if(t&&t.children){ ROOT=t; walk(ROOT,(n)=>{const m=/^b(\d+)$/.exec(n.id||'');if(m)idCounter=Math.max(idCounter,+m[1]+1);}); } }catch(_){}
  normalizeLean();   // migrate any old single-span lean mappings to the list form
  setupSplitters();
  await renderPdf();
  await initLean();
  // a selection lives in exactly one pane: PDF text layer OR Lean code. Read
  // both; whichever matches wins, the other is cleared — never stale.
  document.addEventListener('selectionchange',()=>{ curSel=readSelection(); leanCurSel=readLeanSelection();
    if(curSel) leanCurSel=null; updateSelUI(); });
  $('pages').addEventListener('click', onPdfClick);
  $('pages').addEventListener('dblclick', onPdfDblClick);
  $('leanMap').onclick=mapLean; $('leanUnmap').onclick=removeLeanSel; $('leanNone').onclick=mapLeanNone; $('leanClear').onclick=clearLean;
  $('vOk').onclick=()=>setVerdict('ok'); $('vNotok').onclick=()=>setVerdict('notok'); $('vUndec').onclick=()=>setVerdict('undecidable');
  $('tabBoxes').onclick=()=>switchTab('boxes'); $('tabLean').onclick=()=>switchTab('lean');
  $('labelSel').onchange=(e)=>setLabel(e.target.value);
  $('upLevel').onclick=upLevel; $('upLevelPdf').onclick=upLevel;
  $('mkbox').onclick=makeBox; $('extendbox').onclick=extendBox; $('removebox').onclick=removeSel;
  // link button toggles link mode: arm when idle, cancel when already armed
  $('linkbox').onclick=()=>{ if(linkFrom) cancelLink(); else startLink(); };
  $('confirmlink').onclick=()=>confirmLink();
  $('save').onclick=()=>save(true);
  document.addEventListener('keydown',(e)=>{ const t=document.activeElement; if(t&&(t.tagName==='INPUT'||t.tagName==='TEXTAREA'))return;
    if(e.key==='Escape'&&linkFrom){e.preventDefault();cancelLink();return;}
    if(e.key==='Enter'&&linkFrom&&linkTo){e.preventDefault();confirmLink();return;}
    if(e.key==='l'){e.preventDefault(); if(linkFrom) cancelLink(); else startLink(); return;}
    if(e.key==='n'&&curSel){e.preventDefault();makeBox();}
    if(e.key==='e'&&curSel){e.preventDefault();extendBox();}
    // r removes from whichever pane has the active selection: NL piece or Lean span
    if(e.key==='r'&&curSel){e.preventDefault();removeSel();}
    if(e.key==='r'&&leanCurSel&&selId){e.preventDefault();removeLeanSel();}
    if(e.key==='m'&&leanCurSel&&selId){e.preventDefault();mapLean();}
    if((e.metaKey||e.ctrlKey)&&e.key.toLowerCase()==='s'){e.preventDefault();save(true);}
  });
  window.addEventListener('beforeunload',(e)=>{if(dirty){e.preventDefault();e.returnValue='';}});
}
init();
