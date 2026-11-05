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
let ROOT = { id: 'root', pieces: [], children: [] };
let levelId = 'root';      // CURRENT NODE — new boxes are added as ITS children.
                           // The tree structure is AUTHORED via this, not guessed
                           // from character containment.
let selId = null;          // blue selection = extend/remove target
let curSel = null;         // {start,end} current char-index selection
let dirty = false;
let idCounter = 1;
const freshId = () => 'b' + (idCounter++);
const COLLAPSED = {};

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

/* ───────────────── render PDF + build char sequence ───────────────── */
async function renderPdf(){
  const lib=window['pdfjs-dist/build/pdf']||window.pdfjsLib;
  lib.GlobalWorkerOptions.workerSrc='https://cdn.jsdelivr.net/npm/pdfjs-dist@3.11.174/build/pdf.worker.min.js';
  const pdf=await lib.getDocument('../paper.pdf').promise;
  const host=$('pages'); host.innerHTML=''; pageEls={}; CHARS=''; CHARMETA=[];
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
function spanOf(node){ let x=node.nodeType===3?node.parentElement:node; while(x&&!(x.dataset&&x.dataset.start!==undefined)) x=x.parentElement; return x||null; }
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
function deleteBox(id){ const p=parentOf(id); if(!p) return; const i=p.children.findIndex((c)=>c.id===id); const rm=p.children[i]; p.children.splice(i,1,...rm.children); sortKids(p); if(selId===id)selId=null; if(levelId===id)levelId=p.id; markDirty(); refreshAll(); }
function removePiece(id,idx){ const n=find(id); if(!n)return; n.pieces.splice(idx,1); if(!n.pieces.length){deleteBox(id);return;} markDirty(); refreshAll(); }

/* ───────────────── paint highlights on the PDF ───────────────── */
function render(){ paintHighlights(); renderTree(); updateSelUI(); }
function paintHighlights(){
  for(const p of Object.values(pageEls)) p.hl.innerHTML='';
  // FOCUS VIEW: show the CURRENT LEVEL as an OUTLINE only (no fill, so you see
  // inside it), and its DIRECT CHILDREN as filled highlights. Nothing else is
  // drawn — the display is scoped to the level you're in.
  const level=find(levelId)||ROOT;
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
// draw highlight rects for char range [s,e). opts.outline => just a border (no
// fill); opts.sel => stronger fill + ring for the blue selection.
function drawRange(s,e,color,opts){
  opts=opts||{}; let run=null;
  const flush=()=>{ if(!run)return; const pg=pageEls[run.page]; if(pg){ const d=document.createElement('div'); d.className='hl';
    d.style.left=run.x0+'px'; d.style.top=run.y0+'px';
    d.style.width=(run.x1-run.x0)+'px'; d.style.height=(run.y1-run.y0)+'px';
    if(opts.outline){ d.style.background='rgba(120,120,120,0.10)'; d.style.boxShadow='inset 0 0 0 1px rgba(120,120,120,0.35)'; }  // current level: light grey, see-through
    else { d.style.background=color+(opts.sel?'88':'44'); if(opts.sel) d.style.boxShadow='0 0 0 1.5px '+color; }
    pg.hl.appendChild(d);} run=null; };
  for(let i=s;i<e;i++){ const m=CHARMETA[i]; if(!m){flush();continue;}
    if(run && m.page===run.page && Math.abs(m.y-run.y0)<3){ run.x1=Math.max(run.x1,m.x+m.w); run.y1=Math.max(run.y1,m.y+m.h); }
    else { flush(); run={page:m.page,x0:m.x,y0:m.y,x1:m.x+m.w,y1:m.y+m.h}; } }
  flush();
}

/* ───────────────── tree panel ───────────────── */
function renderTree(){
  const host=$('tree'); host.innerHTML=''; host.appendChild(treeRow(ROOT,true));
  // current-level bar: where new boxes will nest, + a way up
  const bar=$('sellab'); bar.innerHTML='';
  const cur=document.createElement('span'); cur.textContent = levelId==='root'?'paper (top level)':label(find(levelId));
  bar.appendChild(cur);
  if(levelId!=='root'){ const up=document.createElement('button'); up.className='btn'; up.style.cssText='margin-left:8px;padding:0 7px;font-size:11px'; up.textContent='↑ up'; up.onclick=upLevel; bar.appendChild(up); }
}
function label(b){ if(!b) return '(none)'; const ps=pieces(b); if(!ps.length) return '(span)'; const t=CHARS.slice(ps[0].start,ps[0].end).replace(/\s+/g,' ').trim(); return (t.slice(0,30)||'(span)')+(ps.length>1?` …+${ps.length-1}`:''); }
function treeRow(node,isRoot){
  const wrap=document.createElement('div'); const row=document.createElement('div'); row._id=node.id;
  const kids=node.children.length>0, collapsed=!!COLLAPSED[node.id];
  row.className='row'+(node.id===selId?' picked':'')+(node.id===levelId?' level':'');
  const tw=document.createElement('span'); tw.className='twist'+(kids?'':' leaf'); tw.textContent=kids?(collapsed?'▸':'▾'):'·';
  if(kids) tw.onclick=(e)=>{e.stopPropagation();COLLAPSED[node.id]=!collapsed;renderTree();};
  row.appendChild(tw);
  if(!isRoot){const sw=document.createElement('span');sw.className='rswatch';sw.style.background=boxColor(node.id);row.appendChild(sw);}
  const nm=document.createElement('span'); nm.className='rname'; nm.textContent=isRoot?'paper':label(node); row.appendChild(nm);
  // "enter" button: make this node the current level (new boxes nest under it)
  const ent=document.createElement('span'); ent.className='renter'; ent.textContent='⤵'; ent.title='enter: add segments inside this node';
  ent.onclick=(e)=>{e.stopPropagation();enterLevel(node.id);}; row.appendChild(ent);
  if(!isRoot){const del=document.createElement('span');del.className='rdel';del.textContent='✕';del.onclick=(e)=>{e.stopPropagation();deleteBox(node.id);};row.appendChild(del);}
  // single click: select (blue). double click: enter level.
  row.onclick=()=>{ if(!isRoot){ selId=node.id; render(); scrollToChar(pieces(node)[0].start); } };
  row.ondblclick=()=>{ enterLevel(node.id); };
  wrap.appendChild(row);
  // piece sub-rows (navigable) when >1 piece
  if(!isRoot && pieces(node).length>1 && !collapsed){
    const pb=document.createElement('div'); pb.className='children';
    pieces(node).forEach((p,pi)=>{ const pr=document.createElement('div'); pr.className='row piecerow';
      const pad=document.createElement('span');pad.className='twist leaf';pad.textContent='·';pr.appendChild(pad);
      const dot=document.createElement('span');dot.className='rswatch';dot.style.background=boxColor(node.id);dot.style.opacity='.6';pr.appendChild(dot);
      const t=document.createElement('span');t.className='rname';t.textContent=`${pi+1}. ${CHARS.slice(p.start,p.end).replace(/\s+/g,' ').trim().slice(0,22)||'(span)'}`;pr.appendChild(t);
      const del=document.createElement('span');del.className='rdel';del.textContent='✕';del.title='remove this piece';del.onclick=(e)=>{e.stopPropagation();removePiece(node.id,pi);};pr.appendChild(del);
      pr.onclick=()=>{selId=node.id;render();scrollToChar(p.start);}; pb.appendChild(pr); });
    wrap.appendChild(pb);
  }
  if(kids){const box=document.createElement('div');box.className='children';node.children.forEach((c)=>box.appendChild(treeRow(c,false)));wrap.appendChild(box);}
  return wrap;
}
function scrollToChar(i){ const m=CHARMETA[i]; if(!m)return; const pg=pageEls[m.page]; if(!pg)return; $('pdfScroll').scrollTo({top:Math.max(0,pg.wrap.offsetTop+m.y-80),behavior:'smooth'}); }

/* ───────────────── ui glue ───────────────── */
function updateSelUI(){
  const mk=$('mkbox'),ex=$('extendbox'),rm=$('removebox'),info=$('selinfo');
  const box=selId&&find(selId);
  if(curSel){ mk.disabled=false; ex.disabled=!box;
    const overlaps=box&&pieces(box).some((p)=>curSel.start<p.end&&curSel.end>p.start); rm.disabled=!overlaps;
    const lvl=levelId==='root'?'paper':label(find(levelId));
    info.textContent=`“${CHARS.slice(curSel.start,curSel.end).replace(/\s+/g,' ').trim().slice(0,24)}” · n=new under ${lvl}`+(box?` · e=add to “${label(box)}”`:'');
  } else { mk.disabled=true; ex.disabled=true; rm.disabled=true; info.textContent=''; }
}
function clearSel(){ window.getSelection().removeAllRanges(); curSel=null; }
function flash(m){ $('status').textContent=m; setTimeout(()=>{if($('status').textContent===m)$('status').textContent='';},3000); }
function refreshAll(){ paintHighlights(); renderTree(); updateSelUI(); }

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

/* ───────────────── init ───────────────── */
async function init(){
  try{ const t=await fetch('../tree.json').then((r)=>r.ok?r.json():null); if(t&&t.children){ ROOT=t; walk(ROOT,(n)=>{const m=/^b(\d+)$/.exec(n.id||'');if(m)idCounter=Math.max(idCounter,+m[1]+1);}); } }catch(_){}
  setupSplitters();
  await renderPdf();
  document.addEventListener('selectionchange',()=>{ curSel=readSelection(); updateSelUI(); });
  $('mkbox').onclick=makeBox; $('extendbox').onclick=extendBox; $('removebox').onclick=removeSel;
  $('save').onclick=()=>save(true);
  document.addEventListener('keydown',(e)=>{ const t=document.activeElement; if(t&&(t.tagName==='INPUT'||t.tagName==='TEXTAREA'))return;
    if(e.key==='n'&&curSel){e.preventDefault();makeBox();}
    if(e.key==='e'&&curSel){e.preventDefault();extendBox();}
    if(e.key==='r'&&curSel){e.preventDefault();removeSel();}
    if((e.metaKey||e.ctrlKey)&&e.key.toLowerCase()==='s'){e.preventDefault();save(true);}
  });
  window.addEventListener('beforeunload',(e)=>{if(dirty){e.preventDefault();e.returnValue='';}});
}
init();
