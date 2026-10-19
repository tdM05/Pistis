"use strict";
/* The viewer. One unit at a time, at any depth, rendered by one code path.
 *
 * Everything on screen is derived from the files of a unit — `T_F`, `T_N`, `C_N`, `S_F`/`S_N`,
 * `edges` — plus the placement the server computes from the chain. Nothing is derived from which
 * LEVEL the unit sits at. `render()` runs for the root (a Lean file against a lemma) and for
 * `root/1.2/formula` (`D + τ • Matrix.single s j 1` against `D+\tau e_s e_j^{\mathsf T}`) with no
 * branch between them. That is the claim this prototype makes, so the UI had better be one widget.
 *
 * Three rules:
 *   - every region wears its edge's colour faintly at all times, and hovering or pinning raises that
 *     one edge out of the wash. Colour says "an edge claims this"; brightness says "you are on it";
 *   - the bottom strip shows THE ONE EDGE you are on, not a list. Thirteen rows of region text and
 *     reasons is a dump of the annotation; one edge — `T_F`, `T_N` and the `C_N` it is judged
 *     against — is a claim a reader can act on. `j`/`k` walk the rest;
 *   - the only navigation is hover → click → `deeper` / `back`.
 *
 * Spans are UTF-16 offsets, which is exactly what a JS string index is, so a span out of the JSON
 * indexes the rendered text directly — no conversion, nothing to get wrong.
 */

const S = {item:null, path:"root", tree:null, unit:null, hot:null, pin:null,
           elsF:{}, elsN:{}, raw:false, ctx:true, frame:-1};

const $  = (id) => document.getElementById(id);
const el = (tag, cls, txt) => { const e=document.createElement(tag);
  if(cls) e.className=cls; if(txt!=null) e.textContent=txt; return e; };

// The edge in view: pinned beats hovered, and `null` means none.
const live = () => (S.pin !== null ? S.pin : S.hot);

// Each edge gets a hue. A region wears it faintly at all times (`wash`/`hair`) and brightly while it
// is the edge you are on (`tint`/`ink`) — same hue, two intensities, so "an edge claims this" and
// "this is the one in view" are both legible at once. The verdict is carried by LINE STYLE, not by
// colour, so "which text does this edge touch" and "does it hold" stay separately readable.
const hue  = (i) => (i*53 + 18) % 360;
const wash = (i) => `hsl(${hue(i)} 72% 93.5%)`;
const hair = (i) => `hsl(${hue(i)} 44% 80%)`;
const tint = (i) => `hsl(${hue(i)} 82% 83%)`;
const ink  = (i) => `hsl(${hue(i)} 48% 42%)`;

const toast = (msg) => { const t=$("toast"); t.textContent=msg; t.classList.add("on");
  clearTimeout(toast._t); toast._t=setTimeout(()=>t.classList.remove("on"), 3200); };

async function api(route, body){
  const r = await fetch(route, body ? {method:"POST", body:JSON.stringify(body)} : undefined);
  const j = await r.json();
  if(!r.ok || j.error){ toast(j.error || `${r.status} ${route}`); throw new Error(j.error); }
  return j;
}

/* ------------------------------------------------------------------ regions → runs
 * Regions may OVERLAP (in `item1` the root's `def` and `thm` share the `variable` line — that is the
 * "move it into the target" move: text two sentences both talk about belongs to both regions) and may
 * be NON-CONTIGUOUS. So a pane cannot be a list of regions; it is a list of runs, where a run is a
 * maximal stretch of characters owned by the same SET of regions. */
function runs(text, regions){
  const marks = new Set([0, text.length]);
  for(const r of regions) for(const [a,b] of r.spans){ marks.add(a); marks.add(b); }
  const pts = [...marks].filter(p=>p>=0 && p<=text.length).sort((x,y)=>x-y);
  const out = [];
  for(let i=0;i<pts.length-1;i++){
    const a=pts[i], b=pts[i+1];
    if(a>=b) continue;
    const owners = regions.filter(r=>r.spans.some(([x,y])=>x<=a && b<=y)).map(r=>r.idx);
    out.push({a, b, owners});
  }
  return out;
}

// Which edges touch a region, per side. A region in two edges is text two sentences share.
function edgesOf(side, idx){
  return S.unit.edges.map((e,i)=>[e,i]).filter(([e])=>e[side]===idx).map(([,i])=>i);
}

// A run carries its identity in data attributes and its colours in custom properties. The faint pair
// is worn immediately, so you can see where the annotation is before touching anything; `paint` adds
// `lit` to raise the one edge in view. Text in no region at all (whitespace, comments, `--|` markers)
// is greyed, because that is a fact about the text rather than a claim about an edge: it is what
// coverage exempts.
function dressRun(e, side, owners){
  e.className = "run" + (owners.length ? "" : " bare") + (owners.length>1 ? " multi" : "");
  if(owners.length){
    const edges = owners.flatMap(o=>edgesOf(side, o));
    if(edges.length){
      e.style.setProperty("--edge", ink(edges[0]));
      e.style.setProperty("--tint", tint(edges[0]));
      e.style.setProperty("--wash", wash(edges[0]));
      e.style.setProperty("--hair", hair(edges[0]));
    }
    e.dataset.regs = owners.join(",");
    e.dataset.side = side;
    e.onmouseenter = () => { if(S.pin===null){ S.hot = edges[0] ?? null; paint(); } };
    e.onmouseleave = () => { if(S.pin===null){ S.hot = null; paint(); } };
    e.onclick = () => {
      const want = edges[0] ?? null;
      S.pin = S.pin===want ? null : want;
      if(S.pin!==null) reveal(S.pin, side==="f" ? "n" : "f");  // scroll the OTHER pane, not this one
      paint();
    };
  }
  return e;
}

/* ------------------------------------------------------------------ LaTeX
 * The prose is LaTeX, and a region may cut into a formula — `D+\tau e_s e_j^{\mathsf T}` is half of
 * one. A piece of text that is a WHOLE formula is typeset; a piece that is part of one is shown as
 * its source in monospace. Nothing is ever re-flowed to make the typesetting prettier: the
 * characters on screen are the characters the spans index. */
const KATEX_MACROS = {"\\im":"\\operatorname{im}", "\\rank":"\\operatorname{rank}",
  "\\R":"\\mathbb{R}", "\\N":"\\mathbb{N}", "\\Z":"\\mathbb{Z}", "\\Q":"\\mathbb{Q}",
  "\\C":"\\mathbb{C}", "\\supp":"\\operatorname{supp}"};

function mathSegments(text){
  const re = /\$\$([\s\S]+?)\$\$|\\\[([\s\S]+?)\\\]|\$([^$\n]+?)\$|\\\(([\s\S]+?)\\\)/g;
  const out = []; let m;
  while((m = re.exec(text))){
    const tex = m[1] ?? m[2] ?? m[3] ?? m[4];
    const d = (m[0].length - tex.length) / 2;
    out.push({s:m.index, e:re.lastIndex, is:m.index+d, ie:re.lastIndex-d,
              display:m[1]!=null || m[2]!=null, tex});
  }
  return out;
}

function katexInto(e, tex, display){
  if(window.__noKatex || !window.katex) return false;
  try{
    e.innerHTML = katex.renderToString(display ? "\\displaystyle "+tex : tex,
                                       {displayMode:false, throwOnError:true, macros:KATEX_MACROS});
    return true;
  }catch(err){ return false; }
}

// A stretch of text, split at formula boundaries: [{a, b, seg|null}].
function pieces(run, segs){
  const cuts = new Set([run.a, run.b]);
  for(const g of segs) for(const p of [g.s, g.e]) if(p>run.a && p<run.b) cuts.add(p);
  const pts = [...cuts].sort((x,y)=>x-y);
  const out = [];
  for(let i=0;i<pts.length-1;i++){
    const a=pts[i], b=pts[i+1];
    out.push({a, b, seg: segs.find(g=>g.s<b && a<g.e) || null});
  }
  return out;
}

// Fill `holder` with text[a,b), typesetting whole formulae and showing cut ones as source.
function fill(holder, text, run, segs){
  for(const p of pieces(run, segs)){
    const raw = text.slice(p.a, p.b);
    if(p.seg && p.seg.s===p.a && p.seg.e===p.b){
      const m = el("span");
      holder.appendChild(katexInto(m, p.seg.tex, p.seg.display) ? m : el("span", "rawmath", raw));
    }else if(p.seg){
      holder.appendChild(el("span", "rawmath", raw));
    }else{
      holder.appendChild(document.createTextNode(raw));
    }
  }
  return holder;
}

const prose = (host, text, raw) =>
  fill(host, text, {a:0, b:text.length}, raw ? [] : mathSegments(text));

/* ------------------------------------------------------------------ the two panes */
function renderF(){
  const text = S.unit.T_F, body = $("bodyF"), nums = $("linesF");
  body.textContent = ""; S.elsF = {};
  for(const r of runs(text, S.unit.F)){
    const e = dressRun(el("span", null, text.slice(r.a, r.b)), "f", r.owners);
    body.appendChild(e);
    for(const o of r.owners) (S.elsF[o] = S.elsF[o] || []).push(e);
  }
  const n = text.split("\n").length;
  nums.textContent = n>=4 ? Array.from({length:n}, (_,i)=>i+1).join("\n") : "";
  $("subF").textContent = `${S.unit.F.length} regions · ${n} line${n===1?"":"s"} · `
    + (S.unit.provenance.kind==="file" ? S.unit.provenance.T_F
       : `S_F[${S.unit.provenance.f}] of ${S.unit.provenance.parent}`);
}

function renderN(){
  const text = S.unit.T_N, body = $("bodyN");
  body.textContent = ""; S.elsN = {};
  body.classList.toggle("src", S.raw);
  const segs = S.raw ? [] : mathSegments(text);
  for(const r of runs(text, S.unit.N)){
    const holder = fill(dressRun(el("span"), "n", r.owners), text, r, segs);
    body.appendChild(holder);
    for(const o of r.owners) (S.elsN[o] = S.elsN[o] || []).push(holder);
  }
  const w = text.trim().split(/\s+/).length;
  $("subN").textContent = `${S.unit.N.length} regions · ${w} words · `
    + (S.unit.provenance.kind==="file" ? S.unit.provenance.T_N
       : `S_N[${S.unit.provenance.n}] of ${S.unit.provenance.parent}`);
}

/* ------------------------------------------------------------------ the rails
 * Two different things, kept apart on purpose.
 *
 * LEFT — "where": this unit's target inside the step it was cut from, derived from the chain. There
 * is no `C_F` and there is not going to be one: on the formal side you can always rewrite the file
 * so the clause you need is in the target, so an authored citation would be a transcription of text
 * that could have been a span. Chips step the frame out to `Proof.lean`.
 *
 * RIGHT — `C_N`: the sentences of the PAPER a piece of prose must be read against, authored, each
 * with a reason. This one has to exist, because the paper cannot be rewritten: "is still supported on
 * $T$" needs a definition thirteen lines earlier in another paragraph, and widening `T_N` that far
 * would swallow the whole document. Stored as spans into the root's `T_N`, so the text here is
 * sliced, not transcribed, and `check.py` check 9 proves no citation overlaps the prose it is context
 * for. It hangs off the NL REGION, not off the unit, which is what makes it always present: the
 * root's own target is the whole paper and so can have no context at all, while its regions have
 * thirteen edges' worth. The rail follows the live edge and falls back to every region of the unit. */
function renderWhere(){
  const frames = S.unit.placement || [];
  const host = $("ctxF");
  host.textContent = "";
  host.classList.toggle("off", !S.ctx || !frames.length);
  if(!S.ctx || !frames.length) return;

  const pick = Math.min(Math.max(S.frame < 0 ? frames.length + S.frame : S.frame, 0),
                        frames.length - 1);
  const bar = el("div", "ctx-bar");
  bar.appendChild(el("span", "ctx-label", "where"));
  frames.forEach((fr,i)=>{
    const chip = el("button", "chip" + (i===pick ? " on" : ""), fr.loc);
    chip.title = `${fr.path}${fr.title ? " — " + fr.title : ""}`;
    chip.onclick = () => { S.frame = i - frames.length; renderWhere(); };
    bar.appendChild(chip);
  });
  bar.appendChild(el("span", "ctx-note", "derived from the chain"));
  host.appendChild(bar);

  const fr = frames[pick];
  const seen = el("div", "ctx-text mono");
  let hit = null;
  for(const r of runs(fr.T_F, [{idx:0, spans:fr.F}])){
    const sp = el("span", r.owners.length ? "ctx-hit" : null, fr.T_F.slice(r.a, r.b));
    if(r.owners.length && !hit) hit = sp;
    seen.appendChild(sp);
  }
  host.appendChild(seen);
  centre(seen, hit);
}

// The citations of one NL region. `null` (a ⊥ formal side) has none, by definition.
const citesOf = (n) => (n===null ? [] : ((S.unit.N[n] || {}).C_N || []));

// One citation as a line: where in the paper, what it says, and its reason on hover and on click.
function citeLine(c, prefix, on){
  const item = el("div", "cite" + (on ? " on" : ""));
  item.title = c.why;                         // the reason, one keystroke away rather than in the way
  item.appendChild(el("span", "cite-at", prefix ? `${prefix} [${c.spans[0][0]}]`
                                                : `[${c.spans[0][0]}]`));
  item.appendChild(prose(el("span", "cite-text"), c.text, S.raw));
  item.onclick = () => toast(c.why);          // and one click away, for the ones worth reading
  return item;
}

// The rail lists EVERY region's citations, always, and marks the live edge's — rather than swapping
// its contents when you hover. Swapping was the first attempt and it made the rail change height,
// which moved the pane under it out from under the pointer. The list is a stable reference; the one
// edge in view gets its own copy in the card at the bottom.
function renderCN(){
  const host = $("ctxN");
  const lit = live(), e = lit===null ? null : S.unit.edges[lit];
  const on = e && e.n!==null ? e.n : null;
  const shown = S.unit.N.flatMap(r=>(r.C_N||[]).map(c=>[c, r.loc, r.idx===on]));
  host.textContent = "";
  host.classList.toggle("off", !S.ctx || !shown.length);
  if(!S.ctx || !shown.length) return;

  const mine = shown.filter(([,,hit])=>hit).length;
  const bar = el("div", "ctx-bar");
  bar.appendChild(el("span", "ctx-label", "C_N"));
  bar.appendChild(el("span", "ctx-count",
    `${shown.length} citation${shown.length===1?"":"s"} into the paper`));
  bar.appendChild(el("span", "ctx-note", on===null ? "authored · hover for why"
    : `${mine} for T_N ${S.unit.N[on].loc} · hover for why`));
  host.appendChild(bar);

  const seen = el("div", "ctx-text many");
  let first = null;
  for(const [c, prefix, hit] of shown){
    const line = citeLine(c, prefix, hit);
    if(hit && !first) first = line;
    seen.appendChild(line);
  }
  host.appendChild(seen);
  centre(seen, first);
}

// Scroll a rail so the marked text is in the middle. Measured, not computed from `offsetTop`: these
// are inline spans with no positioned ancestor, and KaTeX nests several levels of its own.
function centre(box, hit){
  if(!hit) return;
  const hr = hit.getBoundingClientRect(), sr = box.getBoundingClientRect();
  if(hr.height) box.scrollTop += (hr.top - sr.top) - (sr.height - hr.height)/2;
}

/* ------------------------------------------------------------------ ribbons
 * ONE ribbon: the live edge. A curve from its formal region to its NL region, or a stub into the
 * gutter ending in ⊥ when the labeler said there is nothing on the other side. */
function anchor(map, idx, scroll){
  const e = (map[idx] || [])[0];
  if(!e) return null;
  const rects = e.getClientRects();
  if(!rects.length) return null;
  const sr = scroll.getBoundingClientRect();
  const y = rects[0].top + rects[0].height/2;
  const at = Math.min(Math.max(y, sr.top + 3), sr.bottom - 3);
  return {y: at, clipped: at !== y};      // clamped, so an off-screen region is never drawn as ⊥
}

function ribbons(){
  const svg = $("ribbons"), g = $("gutter").getBoundingClientRect();
  svg.textContent = "";
  const i = live();
  if(i===null || !S.unit.edges[i]) return;
  const e = S.unit.edges[i], W = g.width;
  const aF = e.f===null ? null : anchor(S.elsF, e.f, $("scrollF"));
  const aN = e.n===null ? null : anchor(S.elsN, e.n, $("scrollN"));
  const clipped = (aF && aF.clipped) || (aN && aN.clipped);
  const mk = (tag, attrs, txt) => {
    const n = document.createElementNS("http://www.w3.org/2000/svg", tag);
    for(const k in attrs) n.setAttribute(k, attrs[k]);
    if(txt!=null) n.textContent = txt;
    svg.appendChild(n); return n;
  };
  const style = {stroke: e.v===0 ? "var(--bad)" : (e.f===null||e.n===null) ? "var(--bot)" : ink(i),
                 "stroke-width": 2.4, "stroke-opacity": clipped ? .35 : 1,
                 "stroke-dasharray": e.v===null ? "4 3" : "none"};
  if(aF && aN){
    const y1 = aF.y - g.top, y2 = aN.y - g.top;
    mk("path", {d:`M 0 ${y1} C ${W*.45} ${y1} ${W*.55} ${y2} ${W} ${y2}`, ...style});
    if(e.v===0) mk("text", {x:W/2, y:(y1+y2)/2 - 8, fill:"var(--bad)"}, "✗");
  }else if(aF || aN){
    const left = !!aF, y = (aF || aN).y - g.top;
    mk("path", {d: left ? `M 0 ${y} L ${W*.36} ${y}` : `M ${W} ${y} L ${W*.64} ${y}`, ...style});
    mk("text", {x: left ? W*.46 : W*.54, y, fill:"var(--bot)"}, "⊥");
  }
}

// Bringing an edge's regions into view — a ribbon is only an argument if both ends show.
function reveal(i, sides = "fn"){
  const e = S.unit.edges[i];
  if(!e) return;
  for(const [side, map, idx] of [["f", S.elsF, e.f], ["n", S.elsN, e.n]]){
    if(!sides.includes(side)) continue;
    const node = idx===null ? null : (map[idx] || [])[0];
    if(node) node.scrollIntoView({block:"center", inline:"nearest"});
  }
}

/* ------------------------------------------------------------------ the one edge
 * What the bottom of the screen used to be: every edge of the unit, six columns wide, reasons and
 * region text in full. That is the annotation dumped out, and it drowns the two panes it is supposed
 * to explain. Now it is the live edge only — its two spans, its verdict, its reason — and `j`/`k`
 * walk the rest. Nothing is hidden; it is one at a time instead of all at once. */
function renderEdge(){
  const host = $("edgebody"), i = live();
  host.textContent = "";
  const st = S.unit.status;
  $("tally").innerHTML = `<b>${st.edges}</b> edges &middot; ⊥ <b>${st.bot}</b>`
    + ` &middot; open <b>${st.open_edges.length}</b> &middot; fail <b>${st.bad_edges.length}</b>`
    + (st.inversions.length ? ` &middot; crossings <b>${st.inversions.length}</b>` : "");

  if(i===null || !S.unit.edges[i]){
    $("edgeno").textContent = "edge";
    host.appendChild(el("div", "nothing",
      "hover a span in either pane to see the edge it belongs to — or press j to walk them"));
    return;
  }
  const e = S.unit.edges[i];
  $("edgeno").textContent = `edge ${i}`;
  const card = el("div", "card" + (S.pin===i ? " pinned" : ""));
  card.style.setProperty("--edge", e.v===0 ? "var(--bad)" : ink(i));

  for(const [side, tag, regs, key] of
      [["f", "T_F", S.unit.F, "f"], ["n", "T_N", S.unit.N, "n"]]){
    const row = el("div", "erow");
    const t = el("span", "tag");
    t.innerHTML = tag.replace("_F", "<sub>F</sub>").replace("_N", "<sub>N</sub>");
    row.appendChild(t);
    const idx = e[key];
    if(idx===null){
      row.appendChild(el("span", "etext isbot", "⊥  the labeler says there is nothing here"));
    }else{
      const r = regs[idx];
      row.appendChild(el("span", "eloc", r.loc));
      const txt = el("span", "etext" + (side==="f" ? " mono" : ""));
      if(side==="f") txt.textContent = r.text;
      else prose(txt, r.text, S.raw);
      row.appendChild(txt);
      row.onmouseenter = () => reveal(i, side);
    }
    card.appendChild(row);
  }

  // The third row, and the reason it is here rather than only in the rail: the two rows above are a
  // claim about this Lean and this prose, and whether the claim holds depends on what the prose is
  // allowed to assume. An edge card without its `C_N` is a verdict with its premises off screen.
  const cites = citesOf(e.n);
  const crow = el("div", "erow");
  const ct = el("span", "tag"); ct.innerHTML = "C<sub>N</sub>";
  crow.appendChild(ct);
  if(!cites.length){
    crow.appendChild(el("span", "etext isbot", e.n===null
      ? "— no prose on this edge, so nothing to read it against"
      : "none authored — this prose is ⊥ on the formal side, so no edge claims it"));
  }else{
    const box = el("span", "etext cites");
    for(const c of cites) box.appendChild(citeLine(c, null));
    crow.appendChild(box);
  }
  card.appendChild(crow);

  const ctl = el("div", "erow ctl");
  const sel = el("select", "vsel " + (e.v===1 ? "v1" : e.v===0 ? "v0" : "vn"));
  for(const [v,label] of [["", "· open"], ["1", "✓ holds"], ["0", "✗ fails"]]){
    const o = el("option", null, label); o.value = v; o.selected = String(e.v ?? "")===v;
    sel.appendChild(o);
  }
  ctl.appendChild(sel);
  const why = el("textarea", "why");
  why.rows = 2; why.value = e.why || "";
  why.placeholder = "why — the sentence a reader would need, in order to agree with the verdict";
  why.onblur = () => { if((why.value||"") !== (e.why||"")) saveEdge(i, sel.value, why.value, sel); };
  sel.onchange = () => saveEdge(i, sel.value, why.value, sel);
  ctl.appendChild(why);
  if(e.child){
    const mark = el("span", "refmark", `▾ refinable — ${e.child}`);
    mark.title = "pin this edge and press “deeper”";
    ctl.appendChild(mark);
  }
  card.appendChild(ctl);
  host.appendChild(card);
}

async function saveEdge(i, v, why, sel){
  if(v !== "" && !String(why).trim()){
    toast("a judged edge needs a reason — write one, then set the verdict");
    sel.value = String(S.unit.edges[i].v ?? "");
    const box = sel.closest(".card").querySelector(".why");
    if(box) box.focus();
    return;
  }
  S.unit = await api("/api/edge", {item:S.item, path:S.unit.path, i, v:v===""?null:v, why});
  renderEdge(); paint();
  S.tree = (await api(`/api/tree?item=${S.item}`)).tree;
  renderBadges();
}

/* ------------------------------------------------------------------ chrome */
function renderCrumbs(){
  const nav = $("crumbs");
  nav.textContent = "";
  nav.appendChild(el("span", "sep", S.item));
  S.unit.crumbs.forEach((c)=>{
    nav.appendChild(el("span", "sep", "/"));
    const a = el("a", c.path===S.unit.path ? "here" : null, c.loc);
    a.href = "#" + c.path;
    a.onclick = (ev) => { ev.preventDefault(); go(c.path); };
    nav.appendChild(a);
  });
  if(S.unit.title) nav.appendChild(el("span", "sep", "— " + S.unit.title));
}

function renderBadges(){
  const host = $("badges"), st = S.unit.status;
  host.textContent = "";
  const add = (txt, cls) => { const b = el("span", "badge " + (cls||""));
    b.innerHTML = txt; host.appendChild(b); };
  const node = find(S.tree, S.unit.path);
  if(S.unit.children.length) add(`<b>${node ? node.label : st.own_label}</b> subtree`,
                                 node ? node.label : "");
  add(`<b>${st.own_label}</b> here`, st.own_label);
  for(const side of ["F", "N"]){
    const c = st.coverage[side];
    add(`T<sub>${side}</sub> <b>${c.covered}/${c.total}</b>`, c.complete ? "" : "unfaithful");
  }
  $("donebox").checked = S.unit.done;
}

// The two navigation buttons, and the hint that explains what they are waiting for.
function renderNav(){
  const pinned = S.pin===null ? null : S.unit.edges[S.pin];
  const child = pinned && pinned.child;
  const up = S.unit.crumbs.length > 1 ? S.unit.crumbs.at(-2) : null;

  const back = $("back"), deeper = $("deeper");
  back.disabled = !up;
  back.title = up ? `up to ${up.path}   (Esc, or ←)` : "this is the root";
  deeper.disabled = !child;
  deeper.textContent = child ? `▾ deeper: ${child}` : "▾ deeper";
  deeper.title = child ? `open ${S.unit.path}/${child} in this same view   (Enter, or →)`
    : S.pin===null ? "pin an edge first — click a span in either pane"
    : "the pinned edge is not refined; refining it means making a child unit in annotate_item1.py";

  $("pinhint").innerHTML = S.pin===null
    ? "hover to look &middot; click to pin &middot; <b>j</b>/<b>k</b> to walk"
    : `pinned &middot; Esc to unpin` + (child ? ` &middot; <b>▾ deeper</b> opens ${child}` : "");
}

function find(node, path){
  if(!node) return null;
  if(node.path === path) return node;
  for(const k in node.children){ const hit = find(node.children[k], path); if(hit) return hit; }
  return null;
}

/* ------------------------------------------------------------------ highlight */
function paint(){
  const lit = live();
  const want = {f:new Set(), n:new Set()};
  if(lit!==null && S.unit.edges[lit]){
    const e = S.unit.edges[lit];
    if(e.f!==null) want.f.add(e.f);
    if(e.n!==null) want.n.add(e.n);
  }
  for(const node of document.querySelectorAll("#bodyF .run, #bodyN .run")){
    const regs = (node.dataset.regs||"").split(",").filter(x=>x!=="").map(Number);
    node.classList.toggle("lit", regs.some(r=>want[node.dataset.side].has(r)));
  }
  renderEdge();
  renderCN();            // the rail follows the live edge: its region's context, not the unit's
  renderNav();
  ribbons();
}

/* ------------------------------------------------------------------ navigation */
async function go(path){
  S.path = path;
  S.unit = await api(`/api/unit?item=${S.item}&path=${encodeURIComponent(path)}`);
  S.hot = S.pin = null;
  S.frame = -1;                        // the nearest ancestor, which is what you almost always want
  history.replaceState(null, "", "#" + path);
  render();
}

const deeper = () => {
  const e = S.pin===null ? null : S.unit.edges[S.pin];
  if(e && e.child) go(S.unit.path + "/" + e.child);
};
const back = () => { if(S.unit.crumbs.length > 1) go(S.unit.crumbs.at(-2).path); };

// `j`/`k`: pin the next/previous edge. The way to see all of them, one at a time.
function step(d){
  const n = S.unit.edges.length;
  if(!n) return;
  const at = live();
  S.pin = at===null ? (d>0 ? 0 : n-1) : (at + d + n) % n;
  S.hot = null;
  reveal(S.pin);
  paint();
}

function render(){
  renderCrumbs(); renderF(); renderN(); renderWhere(); renderBadges();
  requestAnimationFrame(paint);        // `paint` draws `C_N`, since it follows the live edge
}

async function boot(){
  const t = await api("/api/tree");
  S.item = t.item; S.tree = t.tree;
  await go(location.hash.replace(/^#/, "") || "root");

  $("back").onclick = back;
  $("deeper").onclick = deeper;
  $("raw").onchange = (e) => { S.raw = e.target.checked; renderN(); renderCN(); paint(); };
  $("ctxon").onchange = (e) => { S.ctx = e.target.checked; renderWhere(); renderCN(); paint(); };
  $("donebox").onchange = async (e) => {
    S.unit = await api("/api/done", {item:S.item, path:S.unit.path, done:e.target.checked});
    S.tree = (await api(`/api/tree?item=${S.item}`)).tree;
    renderBadges();
  };
  for(const id of ["scrollF", "scrollN"]) $(id).addEventListener("scroll", ribbons, {passive:true});
  window.addEventListener("resize", ()=>{ ribbons(); });
  window.addEventListener("keydown", (ev)=>{
    if(ev.target.closest("textarea,select,input")) return;
    if(ev.key==="Escape"){ if(S.pin!==null){ S.pin = null; paint(); } else back(); }
    if(ev.key==="Enter" || ev.key==="ArrowRight") deeper();
    if(ev.key==="ArrowLeft" || ev.key==="u") back();
    if(ev.key==="j" || ev.key==="ArrowDown") step(1);
    if(ev.key==="k" || ev.key==="ArrowUp") step(-1);
  });
  // KaTeX loads deferred; once it is there, the prose is worth drawing again.
  window.addEventListener("load", ()=>{ if(S.unit){ renderN(); renderCN(); paint(); } });
}

boot();
