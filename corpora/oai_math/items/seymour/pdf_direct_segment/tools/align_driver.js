// align_driver — ties the pieces together: given a FOL definition/theorem box id,
// extract its Lean decl, normalize, align, and return {alignment, findings}.
//
// Pure except for extract() (which shells to lean, cached). Shared by the CLI
// (inspect.js --align) and the server (/align endpoint for the UI).
import { readFileSync } from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import { normalize, peelBinders, peelTypeBinders, constNames } from './lean_normalize.js';
import { makeAligner } from './align.js';
import { extract } from './lean_extract/extract.js';
import { surface, locate, pretty } from './lean_spans.js';
import { routeStepToProp } from './llm_route.js';

const SEG_DIR = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');   // pdf_direct_segment/

// Align one FOL box (a definition or theorem) against its Lean decl.
//   core    : makeCore(schema) result
//   root    : the annotation ROOT
//   box     : the FOL box (must be in dict.decls)
//   chars   : the global CHARS string (for symbol slugs)
//   dict    : lean_dict.json  ({decls, symbols})
// Returns { ok, reason?, alignment?, findings?, leanDecl? }.
export function alignBox({ core, root, box, chars, dict, llm }) {
  const C = core;
  // PROOF: if this box sits inside a `proof` that has a Lean-proof association
  // (dict.proofs), do STEP-BY-STEP proof alignment instead of statement alignment —
  // same matcher, same lean_spans span machinery, same result shape (so the UI's
  // existing "align Lean" paints it). Dispatch before the statement decl walk-up.
  { let p = box; while (p && !(dict.proofs && dict.proofs[p.id])) p = C.parentOf(root, p.id);
    if (p) return alignProof({ core, root, proofBox: p, chars, dict, llm }); }
  // align works at the box that carries a Lean decl association. If `box` is
  // INSIDE such a box (e.g. a sub-formula), walk up to the nearest ancestor that
  // has one — so aligning from anywhere inside a definition aligns the definition.
  let target = box;
  while (target && !(dict.decls && dict.decls[target.id])) target = C.parentOf(root, target.id);
  if (!target) return { ok: false, reason: `no Lean decl associated with ${box.id} or any ancestor (add it to lean_dict.json → decls)` };
  box = target;
  const assoc = dict.decls[box.id];
  let raw; try { raw = extract({ decl: assoc.decl, srcFile: assoc.src }); }
  catch (e) { return { ok: false, reason: 'lean extract failed: ' + e.message }; }

  const concrete = C.labelConcrete(box.label);
  const symText = (x) => { const ps = C.pieces(x); if (!ps.length) return '∅'; return chars.slice(ps[0].start, ps[0].end).replace(/\s+/g, ' ').trim().replace(/ /g, '_'); };

  // Lean side: a `def` elaborates to `fun <inputs> => body`. Peel the lam-binders
  // (the inputs) to reach the body (which the FOL `body` slot aligns against).
  // For a theorem the value is a proof; we align the TYPE (the statement) instead.
  const normVal = raw.value && raw.value.kind ? normalize(raw.value) : null;
  const normType = normalize(raw.type);
  // the decl's input binders with the SET OF CONSTS in each binder's type, so the
  // aligner can VERIFY type-vs-prop discharges (e.g. `real` only if a binder's
  // type mentions `Real`). Pulled from the TYPE (which carries the binder types).
  const typeBinders = peelTypeBinders(raw.type).map((b, i) => ({ binder: b.binder, info: b.info, dom: b.dom, typeConsts: constNames(b.dom || {}), isProp: !!(raw.binderProps && raw.binderProps[i]) }));
  const A = makeAligner(C, dict.symbols || {}, symText, { binders: typeBinders, tuples: dict.tuples || {}, root, links: root.links || [], decls: dict.decls || {} });

  // attach SOURCE POSITIONS (from the parsed syntax tree, raw.binders) to the Expr
  // binders, so inputs↔binder-NAME and conditions↔binder-TYPE spans resolve to exact
  // source ranges. raw.binders is the full ordered source binder list (the `variable`
  // line(s) AND the signature); the elaborated Expr keeps only the binders the decl
  // actually uses (e.g. an UNUSED `variable` binder is dropped), always a SUFFIX-matching
  // subsequence — the decl's own binders are present in both and sit at the END.
  // The elaborated binders are a SUBSEQUENCE of the source binders (unused ones — e.g.
  // an unused `[Fintype]` — are dropped, possibly from the MIDDLE), same order. Reconcile
  // by walking both in order: a NAMED elaborated binder matches the next source binder
  // with the same name; an INSTANCE binder (`instImplicit`, whose hygienic elaborated
  // name never text-matches) matches the next source INSTANCE binder (collected as a
  // bracketed `[…]`). This fixes both the middle-drop (def's unused Fintypes) and the
  // anonymous-instance case that the old pure name-match choked on.
  {
    const srcBuf = (() => { try { return readFileSync(path.join(SEG_DIR, deriveLeanRel(assoc)), 'utf8'); } catch (_) { return ''; } })();
    const b2c = srcBuf ? Buffer.from(srcBuf, 'utf8') : null;
    const nameText = (r) => { if (!r || !b2c) return ''; return b2c.slice(r.start, r.stop).toString('utf8').trim(); };
    const isInstSrc = (sb) => nameText(sb.name).startsWith('[');   // anonymous instance binder: collected as the whole `[…]`
    const synB = raw.binders || [];
    let si = 0;
    for (const tb of typeBinders) {
      const wantInst = tb.info === 'instImplicit';
      while (si < synB.length && (wantInst ? !isInstSrc(synB[si]) : nameText(synB[si].name) !== tb.binder)) si++;
      if (si < synB.length) { tb.synName = synB[si].name; tb.synType = synB[si].type; si++; }
    }
  }

  if (concrete === 'definition') {
    const { binders } = peelBinders(normVal || {});
    const lamInputs = binders.filter((b) => b.kind === 'lam');
    let leanBody = normVal; for (let i = 0; i < lamInputs.length; i++) leanBody = leanBody.body;
    const slot = (k) => (box.children || []).find((c) => c.label && c.label[0] === k);
    const bodyBox = slot('body');
    if (!bodyBox) return { ok: false, reason: 'definition has no body slot to align' };

    // The Lean decl is `def Name {I J} [insts] (T) (D) : Prop := body`. Each FOL
    // slot maps to a DIFFERENT part of it (see doc/align-todo.md):
    //   name       → the definiendum (decl name)
    //   inputs     → the binders (typeBinders: I J T D), matched BY NAME
    //   conditions → the binder TYPES (e.g. T⊆I×J ↔ `T : Set (I×J)`), by subject var
    //   body       → the peeled body, via the structural aligner (halts on mismatch)
    // (binder source positions were reconciled above — shared with the theorem path.)
    const children = [];
    children.push(alignName(slot('name'), assoc.decl));
    children.push(alignInputs(slot('inputs'), typeBinders));
    children.push(alignConditions(slot('conditions'), typeBinders));
    children.push(labelNode(bodyBox, A.align(bodyBox, leanBody), 'body'));

    const alignment = { fol: box.id, lean: null, leanNode: null, status: 'match', note: '', children };
    return finish(alignment, assoc, lamInputs, { leanBody, typeBinders, ranges: raw.ranges });
  }
  if (concrete === 'theorem') {
    // theorem = statement + proof. The STATEMENT mirrors a definition, so its slots
    // map to the SAME parts of the decl's signature:
    //   name       → the decl name
    //   inputs     → the binders (typeBinders), matched BY NAME
    //   conditions → the binder TYPES, by subject var
    //   conclusion → the decl's RESULT TYPE: normType with ALL its binders peeled
    // The difference from a def is only WHERE the body comes from: a def's body is the
    // VALUE (after :=); a theorem's conclusion is the TYPE (after the last : before :=).
    // The `proof` (the value) is OUT OF SCOPE for structural alignment (align-todo.md).
    const stmtBox = (box.children || []).find((c) => c.label && c.label[0] === 'statement');
    if (!stmtBox) return { ok: false, reason: 'theorem has no statement slot to align (expected a statement child with name/inputs/conditions/conclusion)' };
    const sslot = (k) => (stmtBox.children || []).find((c) => c.label && c.label[0] === k);
    const conclWrap = sslot('conclusion');
    if (!conclWrap) return { ok: false, reason: 'theorem statement has no conclusion slot to align' };
    // the conclusion wrapper holds ONE formula box — that is what aligns to Lean.
    const conclBox = (conclWrap.children || []).find((c) => C.isFormulaish(c)) || conclWrap;
    // Lean conclusion = the type with ALL binders peeled (used→forall, unused→arrow).
    let leanConcl = normType; for (let i = 0; i < typeBinders.length && leanConcl; i++) leanConcl = leanConcl.body;

    // PEEL THE PRENEX ON BOTH SIDES, then align the MATRICES. A theorem stated the
    // telescoped Lean way lifts its quantifiers + hypotheses into the SIGNATURE binders
    // (the extra inputs x,y,s,j and hypotheses hx,hy,hsj). The NL, however, writes those
    // same quantifiers/hypotheses INSIDE the conclusion as leading `∀ …` / `… →`. So the
    // Lean result type (leanConcl, all binders peeled) is the bare matrix (e.g. the
    // equality x j * y s = 0), while the NL conclusion's OUTER node is a `∀`. Comparing
    // them root-to-root wrongly collides the NL ∀ with the Lean equality. Instead strip
    // each side's leading prenex down to its matrix and align matrix↔matrix, so the real
    // content maps directly. The peeled binders are not lost — they are still reported as
    // the extra inputs/conditions (the ⊥ Lean-only boxes). This also sidesteps the
    // quantifier/hypothesis ORDER differences between the two prenexes.
    const peelFolPrenex = (b) => { let n = b;
      for (;;) { const c = C.labelConcrete(n.label);
        if (c === 'universal' || c === 'existential') { const body = (n.children || []).find((ch) => C.isFormulaish(ch)); if (!body) break; n = body; continue; }
        if (c === 'implication') { const fs = (n.children || []).filter((ch) => C.isFormulaish(ch)); if (fs.length < 2) break; n = fs[fs.length - 1]; continue; }
        break; }
      return n; };
    const peelLeanPrenex = (x) => { while (x && (x.t === 'forall' || x.t === 'arrow')) x = x.body; return x; };
    const nlCore = peelFolPrenex(conclBox);
    const leanCore = peelLeanPrenex(leanConcl);

    const children = [];
    children.push(alignName(sslot('name'), assoc.decl));
    children.push(alignInputs(sslot('inputs'), typeBinders));
    children.push(alignConditions(sslot('conditions'), typeBinders));
    children.push(labelNode(conclBox, A.align(nlCore, leanCore), 'conclusion'));

    const alignment = { fol: box.id, lean: null, leanNode: null, status: 'match', note: '', children };
    return finish(alignment, assoc, [], { leanBody: leanConcl, typeBinders, ranges: raw.ranges, isTheorem: true });
  }
  // bare top-level `formula` box (no statement wrapper): align against the Lean TYPE.
  const alignment = A.align(box, normType);
  return finish(alignment, assoc, [], { leanBody: normType, typeBinders, ranges: raw.ranges });

  // ── slot aligners (definition) ────────────────────────────────────────────
  // wrap a sub-alignment produced by the structural aligner so it is tagged with
  // the FOL slot box it belongs to (keeps the slot visible in the report tree).
  function labelNode(folBox, sub, slotName) {
    // the wrapper is a structural grouping only; the real status/finding lives on
    // `sub` (the aligner's node). Keep the wrapper neutral so the finding is not
    // double-counted (wrapper + sub both carry the same fol id).
    return { fol: null, lean: null, leanNode: null, status: 'match', note: '', slot: slotName, children: [sub] };
  }
  // name ↔ definiendum: the `name` box maps to the decl's own name. The leanNode is
  // a synthetic const so the span walk locates the `def <Name>` occurrence.
  function alignName(nameBox, decl) {
    const leaf = decl.split('.').pop();
    if (!nameBox) return { fol: null, lean: leaf, leanNode: null, status: 'unmapped', note: `Lean defines '${leaf}' but NL has no name slot`, slot: 'name', children: [] };
    return { fol: nameBox.id, lean: leaf, leanNode: { t: 'const', name: leaf }, status: 'leaf', note: `name ↔ ${leaf}`, slot: 'name', children: [] };
  }
  // ONE ordered binder list. There is NO "object vs constraint" distinction in Lean —
  // each binder `(x : τ)` carries BOTH: its NAME x is an input, its TYPE τ is a
  // condition. So inputs and conditions both match POSITIONALLY against the SAME
  // ordered binder list (tbinders), by name and by type respectively.

  // inputs ↔ binder NAMES, positionally. Nth input ↔ name of Nth binder.
  function alignInputs(inputsBox, tbinders) {
    if (!inputsBox) return { fol: null, lean: null, leanNode: null, status: 'match', note: 'no inputs slot', slot: 'inputs', children: [] };
    const invars = (inputsBox.children || []).filter((c) => C.isVariable(c));
    // INPUTS are the DATA binders only. Drop two kinds that are CONDITIONS, not inputs
    // (both are matched by alignConditions): instance binders (`[Fintype I]`, …) and
    // Prop-typed binders (`hD : SupportedOn T D`, `hmax : ∀ A …`). Either, left in, would
    // let an NL input pair with a hypothesis/instance. Sorts (`{I J : Type*}`) stay — they
    // are inputs. (isProp comes from the Lean probe; instImplicit from the binder info.)
    const ibinders = tbinders.filter((tb) => tb.info !== 'instImplicit' && !tb.isProp);
    const kids = []; const n = Math.max(invars.length, ibinders.length);
    for (let i = 0; i < n; i++) {
      const v = invars[i], tb = ibinders[i];
      if (v && tb) kids.push({ fol: v.id, lean: 'binder ' + tb.binder, leanNode: { t: 'var', name: tb.binder }, synPos: tb.synName, status: 'leaf', note: `input #${i + 1} ↔ binder ${tb.binder}`, children: [] });
      else if (v) kids.push({ fol: v.id, lean: '∅', leanNode: null, status: 'mismatch', note: `input #${i + 1} '${symText(v)}' maps to nothing — Lean has no binder at this position`, children: [] });
      else kids.push({ fol: null, lean: 'binder ' + tb.binder, leanNode: { t: 'var', name: tb.binder }, synPos: tb.synName, status: 'unmapped', note: `Lean binder #${i + 1} '${tb.binder}' has no input at this position`, children: [] });
    }
    const bad = kids.some((k) => k.status !== 'leaf');
    return { fol: inputsBox.id, lean: null, leanNode: null, status: bad ? 'mismatch' : 'match', note: '', slot: 'inputs', children: kids };
  }
  // conditions ↔ binder TYPES, positionally. The CONDITIONS are the types of every
  // binder whose type is NOT a universe (Type*/Sort* — those just declare a carrier
  // sort, which is not a condition in FOL). So `{I J : Type*}` are dropped, and e.g.
  // `[Fintype I] [Fintype J] (T : Set (I×J)) (D : Matrix I J ℝ)` give 4 conditions.
  // Nth NL condition ↔ type of the Nth non-sort binder.
  function alignConditions(condsBox, tbinders) {
    if (!condsBox) return { fol: null, lean: null, leanNode: null, status: 'match', note: 'no conditions slot', slot: 'conditions', children: [] };
    const conds = (condsBox.children || []).filter((c) => C.isFormulaish(c));
    // A binder `a : b` with `b` NON-Prop contributes the condition `a ∈ b` (a has type /
    // is in b) — e.g. `D : Matrix I J ℝ` → real_matrix, `T : Set (I×J)` → ⊆, `s : I` → s∈I.
    // The ONLY exclusion is a binder whose type is a UNIVERSE (`{I J : Type*}` / `Sort*`):
    // `I ∈ Type*` is "I is a set", a second-order statement, not a first-order condition.
    const cbinders = tbinders.filter((tb) => !(tb.dom && tb.dom.t === 'sort'));
    // display/highlight span for a condition. Normally the binder's TYPE (`SupportedOn T D`,
    // `x ∈ ker …` — self-explanatory). But when the type is a bare sort-VARIABLE (`s : I`),
    // the type alone ("I") is meaningless, so span the WHOLE binder → reads "s : I".
    const condSpan = (tb) => (tb.dom && tb.dom.t === 'var' && tb.synName && tb.synType) ? { start: tb.synName.start, stop: tb.synType.stop } : tb.synType;
    const kids = []; const n = Math.max(conds.length, cbinders.length);
    for (let i = 0; i < n; i++) {
      const cond = conds[i], tb = cbinders[i];
      if (cond && tb) kids.push({ fol: cond.id, lean: 'type of ' + tb.binder, leanNode: tb.dom || null, synPos: condSpan(tb), status: 'leaf', note: `condition #${i + 1} ↔ type of binder ${tb.binder}`, children: [] });
      else if (cond) kids.push({ fol: cond.id, lean: '∅', leanNode: null, status: 'mismatch', note: `condition #${i + 1} maps to nothing — Lean has no binder at this position (NL asserts a hypothesis the Lean statement does not)`, children: [] });
      else kids.push({ fol: null, lean: 'type of ' + tb.binder, leanNode: tb.dom || null, synPos: condSpan(tb), status: 'unmapped', note: `Lean binder #${i + 1} '${tb.binder}' type has no condition at this position`, children: [] });
    }
    const bad = kids.some((k) => k.status !== 'leaf');
    return { fol: condsBox.id, lean: null, leanNode: null, status: bad ? 'mismatch' : 'match', note: '', slot: 'conditions', children: kids };
  }

  function finish(alignment, assoc, lamInputs, extra = {}) {
    // NL text of a FOL box (its highlighted span) — so the report reads in words,
    // not box ids. Empty for implicit boxes.
    const nlText = (id) => { let b = id && C.find(root, id); if (!b) return '';
      // implicit boxes have no span → climb to the nearest spanned ancestor so the
      // report still reads in words (e.g. the containing clause).
      while (b && !(C.pieces(b).length)) b = C.parentOf(root, b.id);
      if (!b) return ''; const ps = C.pieces(b); return ps.length ? chars.slice(ps[0].start, ps[0].end).replace(/\s+/g, ' ').trim() : ''; };

    const spans = {};
    const leanRegions = [];   // (⊥,F) Lean-only judged regions (no FOL box)
    const pieceSpans = [];    // [start,end] of every mapped leaf piece (for gap tiling)
    const containmentErrors = [];   // mapped pieces whose Lean span is OUTSIDE the def span
    let declRegions = null;   // [[lo,hi),…] the decl's Lean span(s): its own body + the variable line(s)
    let text = '', fileField = '', leanSource = '', leanLine = null;
    try {
      const abs = path.join(SEG_DIR, deriveLeanRel(assoc));
      text = readFileSync(abs, 'utf8');
      fileField = deriveLeanRel(assoc);
      // Lean gives source positions as UTF-8 BYTE offsets; JS string indices are
      // UTF-16 code units. Convert a byte offset → JS string index via the byte
      // length of the growing prefix (one pass, memoized by scanning).
      const byteBuf = Buffer.from(text, 'utf8');
      const byteToChar = (byteOff) => byteBuf.slice(0, byteOff).toString('utf8').length;
      const nameLeaf = assoc.decl.split('.').pop();
      // decl start: prefer the EXACT range Lean gives (extra.ranges, from
      // findDeclarationRanges? — 1-based line, 0-based col); fall back to a text
      // search for `def <name>`/`theorem <name>` only if Lean gave no range.
      const lineColToOffset = (ln, col) => { // ln 1-based, col 0-based → char offset
        let off = 0, line = 1; while (line < ln) { const nl = text.indexOf('\n', off); if (nl < 0) return text.length; off = nl + 1; line++; } return off + col; };
        const rg = extra.ranges;
      let declAt = rg && rg.declStart ? lineColToOffset(rg.declStart.line, rg.declStart.col) : -1;
      if (declAt < 0) { for (const kw of ['def ', 'theorem ', 'lemma ']) { const i = text.indexOf(kw + nameLeaf); if (i >= 0) { declAt = i; break; } } }
      const asgn = declAt >= 0 ? text.indexOf(':=', declAt) : text.indexOf(':=');
      // region boundaries within the source:
      //   [sigLo, sigHi)  = the signature (name + binders + result type), before :=
      //   [bodyLo, bodyHi)= the body, after :=
      const sigLo = declAt >= 0 ? declAt : 0;
      const sigHi = asgn >= 0 ? asgn : (declAt >= 0 ? text.indexOf('\n', declAt) : 0);
      let bodyLo = asgn >= 0 ? asgn + 2 : 0;
      let bodyHi = text.indexOf('\n\n', bodyLo); if (bodyHi < 0) bodyHi = text.length;
      const tnl = text.indexOf('\ntheorem', bodyLo); if (tnl >= 0 && tnl < bodyHi) bodyHi = tnl;
      // 1-based line of the decl. (leanSource — the displayed decl text — is set AFTER
      // the tiling below, to the full def span incl. the variable line.)
      if (declAt >= 0) { leanLine = text.slice(0, declAt).split('\n').length; }
      // which source region a slot's spans live in. name/inputs/conditions all live
      // in the SIGNATURE; body lives in the body region. The structural body walk
      // (via leanNode surfaces) locates within the body as before.
      const slotRegion = (slot) => (slot === 'body' || slot == null) ? [bodyLo, bodyHi] : [sigLo, sigHi];
      // walk: allocate a Lean span per node AND decorate the node with NL + Lean
      // text so the UI can render human-readable rows. `slot` threads down from the
      // nearest ancestor that declared one, choosing the source region to search in.
      const walk = (n, lo, hi, slot) => {
        const mySlot = n.slot || slot;
        if (n.slot) { const [rlo, rhi] = slotRegion(n.slot); lo = rlo; hi = rhi; }
        // locate target, in priority:
        //  - synPos : a REAL source range from Lean's parse tree (byte offsets) — an
        //             input → its binder NAME span, a condition → its binder TYPE
        //             span. Exact, no text search. Converted byte→char here.
        //  - else   : surface the elaborated leanNode and search for it in-region.
        let loc = null;
        if (n.synPos) { let a = byteToChar(n.synPos.start), b = byteToChar(n.synPos.stop);
          // trim a leading ": " on a type-ascription range so it points at the type
          while (a < b && (text[a] === ':' || text[a] === ' ')) a++;
          loc = { start: a, end: b }; }
        if (!loc) { const surf = n.leanNode ? surface(n.leanNode) : null; loc = surf ? locate(text, lo, hi, surf) : null; }
        // RECURSE FIRST (within this node's own span if located, else the inherited
        // region) so an operator parent can fall back to its children's extent below.
        const clo = loc ? loc.start : lo, chi = loc ? loc.end : hi;
        (n.children || []).forEach((c) => walk(c, clo, chi, mySlot));
        // ENVELOPE FALLBACK. An INFIX operator (mul `*`, eq `=`) surfaces to a PREFIX form
        // (`HMul.hMul …`, `Eq …`) that never appears literally in the source, so it can't
        // be located directly — but its operands DID locate. For such a MATCHED node (a
        // 'leaf' like mul≡HMul.hMul, or a structural 'match' like the equality), take the
        // envelope [min child start, max child end] as its extent. Mismatches do NOT
        // envelope — they keep the compared-region behavior below.
        // Only for a real ELABORATED-TERM node (has a leanNode), never a structural
        // wrapper (slot wrappers / the alignment root have leanNode:null) — those span
        // disjoint regions (e.g. the `variable` line AND the decl) and must NOT be
        // collapsed into one envelope.
        if (!loc && n.leanNode && (n.status === 'leaf' || n.status === 'match') && (n.children || []).length) {
          let a = Infinity, b = -Infinity;
          for (const c of n.children) { const cs = c._loc; if (cs) { if (cs.start < a) a = cs.start; if (cs.end > b) b = cs.end; } }
          if (b > a) loc = { start: a, end: b };
        }
        n._loc = loc;
        if (loc && n.fol) spans[n.fol] = { file: fileField, start: loc.start, end: loc.end };
        // NO coarse 'approx' fallback for things that simply couldn't be located. The ONE
        // legitimate non-located span is a MISMATCH that WAS compared against a real Lean
        // region (e.g. the body ∧ vs the Lean ∀ body): show that region [lo,hi] so you see
        // WHAT it was compared to, flagged notok below. A 'leaf' that can't be located is
        // NOT a match → it gets no span here and becomes ∅ + notok. No third state.
        else if (n.fol && n.leanNode && n.status === 'mismatch') spans[n.fol] = { file: fileField, start: lo, end: hi };
        n.nl = nlText(n.fol);
        n.leanText = loc ? text.slice(loc.start, loc.end).replace(/\s+/g, ' ').trim() : (n.leanNode ? pretty(n.leanNode) : '');
        // VERDICT ON THE LINK. A judged node ALWAYS yields a link carrying the verdict:
        //  - leaf (ok)    → link to its Lean span, v:ok
        //  - mismatch     → notok link; to its Lean span if it has one, else a link to
        //                   NOTHING (none:true) when it maps to ∅ (no binder/counterpart
        //                   at this position). The verdict is a property of THIS link.
        // slot wrappers (inputs/conditions) carry NO link of their own — they DERIVE
        // by rolling up their children. Every other judged node (leaf, or a mismatch
        // like the body ∧ whose children are only informational) gets a link+verdict.
        const isWrapper = n.slot === 'inputs' || n.slot === 'conditions';
        if (n.fol && !isWrapper) {
          const located = spans[n.fol] && spans[n.fol].start != null;
          // FAITHFUL iff it actually matched AND located to a real Lean span. Otherwise —
          // a mismatch, OR a 'leaf' pairing we cannot confirm in the Lean source — it DID
          // NOT match: a notok link (keeping its located span if it has one, e.g. the body
          // ∧-vs-∀; else linking to ∅). Same two-state shape as the def's ∅ conditions.
          if (n.status === 'leaf' && located) {
            spans[n.fol].v = 'ok';
          } else if (n.status === 'leaf' || n.status === 'mismatch') {
            if (!spans[n.fol]) spans[n.fol] = { none: true };
            spans[n.fol].v = 'notok'; spans[n.fol].why = humanFinding(n); spans[n.fol].cmp = n.leanText || '(nothing)'; spans[n.fol].path = labelPath(n.fol);
          }
        }
        // (⊥, F): a Lean-only piece (fol:null, has a source span) — a compiled binder
        // NL never covers. It's a judged Lean REGION, not keyed to any FOL box, so it
        // goes in its own list. Its verdict: notok (NL omits a piece the Lean
        // statement has). The UI paints these as notok Lean regions.
        if (!n.fol && loc && n.status === 'unmapped') {
          // tag WHICH kind of Lean-only extra this is (input / condition / …), from the
          // slot it belongs to, so the UI can group them into per-kind sub-boxes.
          const kind = mySlot === 'inputs' ? 'input' : mySlot === 'conditions' ? 'condition' : (mySlot || 'other');
          leanRegions.push({ file: fileField, start: loc.start, end: loc.end, v: 'notok', why: n.note, lean: n.leanText, kind });
        }
        // every piece span contributes to the decl's coverage — used after the walk
        // to compute the UNCOVERED gaps (scaffolding: def/:/:=/Prop). Read from
        // spans[fol] (set above, incl. the approx BODY span) so the body region isn't
        // mistaken for an uncovered gap; plus any located non-fol region (⊥ pieces).
        if (n.fol && spans[n.fol] && spans[n.fol].start != null) pieceSpans.push([spans[n.fol].start, spans[n.fol].end]);
        else if (loc) pieceSpans.push([loc.start, loc.end]);
      };
      walk(alignment, bodyLo, bodyHi, null);
      // COMPLETE THE TILING. The def's Lean span is the WHOLE region from the start of
      // the line of its earliest mapped piece (so a `variable {I J …}` line whose
      // binders the def pulls in is included) through the body end. Every char in that
      // region is either in a mapped piece or in a GAP (scaffolding: `variable`, `def`,
      // `(`, `:`, `)`, `: Prop`, `:=`, whitespace) → emitted as a bot_ok region. (Extra
      // binders are bot_notok above.) So the def is fully tiled, every span ok/notok.
      {
        const merged = pieceSpans.slice().filter(([a, b]) => b > a).sort((x, y) => x[0] - y[0]);
        const lineStartOf = (p) => text.lastIndexOf('\n', p - 1) + 1;
        const lineEndOf = (p) => { const i = text.indexOf('\n', p); return i < 0 ? text.length : i; };
        // The decl's Lean region is the DECL ITSELF — not everything from the shared
        // `variable` line onward. For a THEOREM it ENDS at `:=` (the proof after it is
        // not part of the statement); for a def it runs to the body end. We ALSO keep
        // the `variable` line(s) that feed binders. Any declarations BETWEEN the
        // variable line and this decl (other defs/theorems) are EXCLUDED — they are a
        // different decl's text, not this decl's scaffolding. So the region is up to two
        // disjoint blocks (the variable line + the decl), and gaps are tiled WITHIN each
        // block only, never across the chasm of foreign declarations.
        const regionEnd = extra.isTheorem ? (asgn >= 0 ? asgn : sigHi) : bodyHi;
        const declLo = declAt >= 0 ? lineStartOf(declAt) : sigLo;
        const regions = [];
        const pre = merged.filter(([a]) => a < declLo);   // mapped pieces before the decl = the variable line(s)
        if (pre.length) regions.push([lineStartOf(pre[0][0]), lineEndOf(pre[pre.length - 1][1])]);
        regions.push([declLo, regionEnd]);
        declRegions = regions;
        for (const [lo, hi] of regions) {
          let cur = lo;
          for (const [a, b] of merged) {
            if (b <= lo || a >= hi) continue;   // piece not in this block
            const A = Math.max(a, lo), B = Math.min(b, hi);
            if (A > cur) leanRegions.push({ file: fileField, start: cur, end: A, v: 'ok', why: 'formal scaffolding (no NL counterpart)', kind: 'scaffolding', lean: text.slice(cur, A).replace(/\s+/g, ' ') });
            cur = Math.max(cur, B);
          }
          if (cur < hi) leanRegions.push({ file: fileField, start: cur, end: hi, v: 'ok', why: 'formal scaffolding (no NL counterpart)', kind: 'scaffolding', lean: text.slice(cur, hi).replace(/\s+/g, ' ') });
        }
        // displayed decl text = the decl's block(s) (variable line + decl), joined
        leanSource = regions.map(([lo, hi]) => text.slice(lo, hi)).join('\n').trim();
      }
      // CONTAINMENT ENFORCEMENT: every mapped Lean piece span MUST lie within the
      // def's Lean span [declRegion]. A piece outside it means the alignment linked an
      // NL box to Lean text the def doesn't even cover — a hard error, surfaced as a
      // finding (this is the check that was missing when I/J mapped to a line outside
      // the def span).
      if (declRegions && declRegions.length) {
        for (const id in spans) { const sp = spans[id]; if (sp.start == null) continue;
          const inside = declRegions.some(([rlo, rhi]) => sp.start >= rlo && sp.end <= rhi);
          if (!inside) containmentErrors.push({ fol: id, start: sp.start, end: sp.end, text: text.slice(sp.start, sp.end).replace(/\s+/g, ' ').trim() }); }
      }
    } catch (_) { /* best-effort */ }
    // the elaborated/compiled term the aligner actually walked (what it compares
    // against, not the surface text) — pretty-printed for display.
    const leanElaborated = extra.leanBody ? pretty(extra.leanBody) : '';

    // human-readable findings: only real problems (mismatch/unmapped). Each finding
    // carries the FOL object's FULL LABEL PATH, the Lean file path + span it was
    // compared against, the NL text, and the structural note.
    const findings = [];
    (function collect(n) {
      // a slot wrapper (inputs/conditions) carries no finding of its own — its
      // status just reflects its children; the real findings are on the children.
      const isSlotWrapper = n.slot === 'inputs' || n.slot === 'conditions';
      if ((n.status === 'mismatch' || n.status === 'unmapped') && !isSlotWrapper) {
        const sp = n.fol && spans[n.fol];
        const hasLoc = sp && sp.start != null;   // a ∅ (none) span has no position
        findings.push({
          fol: n.fol,
          path: labelPath(n.fol),
          nl: n.nl || '(implicit)',
          lean: n.leanText || n.lean,
          leanLoc: hasLoc ? `${sp.file}:${sp.start}-${sp.end}` : (fileField ? `${fileField}${leanLine ? ':' + leanLine : ''}` : ''),
          message: humanFinding(n),
        });
      }
      (n.children || []).forEach(collect);
    })(alignment);
    // CONTAINMENT violations → hard findings: an NL box linked to Lean text OUTSIDE
    // the def's own span. This must never happen; if it does, it's a real error.
    for (const e of containmentErrors) {
      findings.push({ fol: e.fol, path: labelPath(e.fol), nl: nlText(e.fol) || '(implicit)',
        lean: e.text, leanLoc: `${fileField}:${e.start}-${e.end}`,
        message: `CONTAINMENT ERROR: this maps to Lean text outside the declaration's span ('${e.text}') — a child's Lean span must lie within its parent's` });
    }
    return {
      ok: true, alignment, findings, spans, leanRegions,
      leanDecl: assoc.decl,
      leanFile: fileField, leanLine, leanSource, leanElaborated,
      leanInputs: lamInputs.map((b) => ({ binder: b.binder, info: b.info })),
    };
  }
  // the FULL concrete label path of a FOL box, e.g.
  // "body.formula.compound-formula.connective.conjunction". Generic over all labels
  // (no per-symbol hardcoding) — this is how a finding names the object it concerns.
  function labelPath(id) {
    const b = id && C.find(root, id);
    return b && b.label ? b.label.join('.') : '';
  }
  // turn an alignment node's internal note into a plain-language problem message.
  // The object is named by its FULL LABEL PATH in a SEPARATE field (`path`), so the
  // message itself does NOT repeat it. Derives the FOL kind from the label path's
  // last component (generic, not a hardcoded symbol table) + the Lean kind.
  function humanFinding(n) {
    const obj = labelPath(n.fol);
    const kind = obj ? obj.split('.').pop() : (n.note.match(/FOL (\w+)/) || [])[1] || 'object';
    // one NL variable forced to mean two different Lean terms
    if (/INCONSISTENT/.test(n.note)) {
      const m = n.note.match(/variable (\S+) maps to INCONSISTENT Lean terms \(([^)]+)\)/);
      const v = m ? m[1] : '?';
      const parts = m ? m[2].split(', ').map((x) => x.replace(/^v:|^c:|^app:c:|^app:|^lit:|^tuple:/, '')) : [];
      return `NL ${v} maps to {${parts.join(', ')}}. must be one thing.`;
    }
    // one ∀ vs two ∀ (note mentions "Lean binds another ∀", so test before Lean-only)
    if (/another ∀/.test(n.note)) return `NL binds 1 variable, Lean binds 2. does not match.`;
    // Lean has something NL does not (Lean-only piece / extra binder / extra operand)
    if (n.fol == null || /Lean binds|Lean defines|operand has no FOL|extra Lean/.test(n.note)) return `in Lean, not in NL.`;
    // NL has something Lean does not (maps to nothing / no counterpart)
    if (/maps to nothing|no Lean binder|no Lean counterpart|has no Lean counterpart|operand has no Lean|extra FOL/.test(n.note)) return `in NL, not in Lean.`;
    // body ∧-halt: Lean body is a single non-∧ shape
    const single = n.note.match(/single (\w+)/);
    if (single) return `Lean body is ${plainLean(single[1])}. NL body is ${plainKind(kind)}. does not match.`;
    // count mismatch: N conjuncts vs M
    const cnt = n.note.match(/has (\d+) parts, Lean ∧ has (\d+)/);
    if (cnt) return `NL has ${cnt[1]} parts, Lean has ${cnt[2]}. does not match.`;
    // generic shape mismatch: "… vs Lean X" / "… but Lean is X"
    const vs = n.note.match(/(?:vs|but) Lean (?:is )?(\w+)/);
    if (vs) return `Lean is ${plainLean(vs[1])}. NL is ${plainKind(kind)}. does not match.`;
    return n.note;
  }
  // plain one-word names (no symbols) for the simple body shape-mismatch message.
  function plainLean(t) {
    return ({ forall: 'forall', exists: 'exists', arrow: 'implication', and: 'and', or: 'or', not: 'not', eq: 'equality', mem: 'membership', app: 'application' })[t] || t;
  }
  function plainKind(k) {
    return ({ conjunction: 'and', disjunction: 'or', implication: 'implication', negation: 'not', universal: 'forall', existential: 'exists', equality: 'equality', relation: 'relation' })[k] || k;
  }
  // the .lean file path as stored in box.lean.spans (relative to pdf_direct_segment/,
  // i.e. "lean/MaxSupportKernel.lean") — matches how the Lean pane references files.
  function deriveLeanRel(assoc) {
    const base = assoc.src.split('/').pop();   // MaxSupportKernel.lean
    return 'lean/' + base;
  }
}

// ── PROOF alignment ───────────────────────────────────────────────────────────
// Match each NL proof STEP against the propositions of the proof's Lean decl(s)
// (their `have`-types + hypotheses), and allocate Lean source spans per matched
// piece — the SAME surface+locate span machinery `finish()` uses for a statement,
// just pointed at each matched prop's own source region. Returns the SAME result
// shape as alignBox so the UI's "align Lean" paints it. Unfaithfulness-detector
// semantics: a step is faithful iff SOME prop aligns cleanly; else its closest
// near-miss (most nodes matched) is reported with the divergence.
function alignProof({ core, root, proofBox, chars, dict, llm }) {
  const C = core;
  const assocs = dict.proofs[proofBox.id];
  // LLM routing (which prop an UNFAITHFUL step is intended to match) is on by default;
  // disable via llm:false or PISTIS_NO_LLM=1 (offline/deterministic runs). It never
  // affects the verdict — only which prop the divergence is reported against.
  const llmEnabled = llm !== false && process.env.PISTIS_NO_LLM !== '1';
  const symText = (x) => { const ps = C.pieces(x); if (!ps.length) return '∅'; return chars.slice(ps[0].start, ps[0].end).replace(/\s+/g, ' ').trim().replace(/ /g, '_'); };

  // NL `define`d names → a COPY of their RHS expression box (ids stripped), so `Dτ`
  // INLINES to `D + τeₛeⱼᵀ` for MATCHING (its body, e.g. the leftover τ, is compared)
  // WITHOUT attributing any Lean spans/verdict to the `define`'s own boxes — the copy
  // has no ids, so the span walk skips it and the define box (b550) isn't polluted.
  const stripIds = (b) => ({ ...b, id: undefined, children: (b.children || []).map(stripIds) });
  const nlDefs = {};
  C.walk(proofBox, (n) => {
    if (C.labelConcrete(n.label) !== 'define') return;
    const vs = (n.children || []).find((k) => C.labelConcrete(k.label) === 'variable-symbol');
    const eq = (n.children || []).find((k) => C.labelConcrete(k.label) === 'equality');
    if (!vs || vs.var == null || !eq) return;
    const terms = (eq.children || []).filter((k) => { const c = C.labelConcrete(k.label); return c && c !== 'equality-symbol' && c !== 'commentary'; });
    const rhs = terms.find((t) => !(C.isVariable(t) && t.var === vs.var)) || terms[terms.length - 1];
    if (rhs) nlDefs[vs.var] = stripIds(rhs);
  });

  // ── NL steps: formula/definition-application boxes that are DIRECT children of a
  // proof-structure block (proof / assumption / case) — i.e. the step-level claims. ──
  const BLOCK = new Set(['proof', 'assumption', 'case', 'case-analysis']);
  const isStep = (b) => { const c = C.labelConcrete(b.label); return c === 'definition-application' || C.isFormulaish(b); };
  const steps = [];
  C.walk(proofBox, (n) => {
    if (!isStep(n)) return;
    const par = C.parentOf(root, n.id);
    if (par && BLOCK.has(C.labelConcrete(par.label))) steps.push(n);
  });

  // ── Lean propositions: every `let` (have) and `lam` (hypothesis) binder type of
  // each proof decl, normalized, with its SOURCE REGION located in the .lean file. ──
  const leanRel = (a) => 'lean/' + a.src.split('/').pop();
  const props = [];
  const srcText = {};   // rel -> file text
  const letEnv = {};    // Lean LOCAL let name -> normalized VALUE (E -> D + single …), for zeta
  for (const a of assocs) {
    let raw; try { raw = extract({ decl: a.decl, srcFile: a.src }); } catch (e) { continue; }
    const rel = leanRel(a);
    if (srcText[rel] == null) { try { srcText[rel] = readFileSync(path.join(SEG_DIR, rel), 'utf8'); } catch (_) { srcText[rel] = ''; } }
    const text = srcText[rel];
    const seen = [];
    (function w(n) { if (!n || typeof n !== 'object') return;
      if (n.kind === 'let' && n.type) seen.push([n.binder, n.type]);
      if (n.kind === 'let' && n.value && letEnv[n.binder] == null) { try { letEnv[n.binder] = normalize(n.value); } catch (_) { } }
      if (n.kind === 'lam' && n.dom) seen.push([n.binder, n.dom]);
      for (const k of ['dom', 'body', 'type', 'value', 'fn', 'on']) if (n[k]) w(n[k]);
      if (Array.isArray(n.args)) n.args.forEach((x) => w(x && x.node ? x.node : x)); })(raw.value);
    for (const [nm, ty] of seen) {
      let node; try { node = normalize(ty); } catch (_) { continue; }
      if (!node) continue;
      props.push({ tag: a.decl.split('.').pop() + '.' + nm, binder: nm, node, text, file: rel, region: typeRegion(text, nm) });
    }
  }
  // the aligner, with NL define-inlining + Lean let-zeta (bounded LOCAL unfolds only).
  const A = makeAligner(C, dict.symbols || {}, symText, { binders: [], tuples: dict.tuples || {}, root, links: root.links || [], decls: dict.decls || {}, nlDefs, letEnv });
  // locate the SOURCE region of a binder's TYPE: `have nm : TYPE :=` → the TYPE; a
  // signature/`obtain` hyp `(nm : TYPE)` → the TYPE; else the line the binder is on.
  function typeRegion(text, nm) {
    if (!text) return null;
    const esc = nm.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    let i = text.indexOf('have ' + nm);
    if (i >= 0) { const c = text.indexOf(':', i); if (c >= 0) { const a = text.indexOf(':=', c); let e = a >= 0 ? a : text.indexOf('\n', c); if (e < 0) e = text.length; return [c + 1, e]; } }
    const m = new RegExp('[({\\s]' + esc + '\\s*:').exec(text);
    if (m) { const c = text.indexOf(':', m.index); let e = text.indexOf(')', c); const nl = text.indexOf('\n', c); if (e < 0 || (nl >= 0 && nl < e)) e = nl; if (e < 0) e = text.length; return [c + 1, e]; }
    const j = new RegExp('(^|[^\\w])' + esc + '([^\\w]|$)').exec(text);
    if (j) { const ls = text.lastIndexOf('\n', j.index) + 1; let le = text.indexOf('\n', j.index); if (le < 0) le = text.length; return [ls, le]; }
    return null;
  }

  // ── walk a step's alignment tree, allocating Lean spans within [lo,hi] of the
  // matched prop's source `text` — recurse-first, surface+locate, envelope fallback
  // for infix ops; a mismatch with no located span falls back to the whole region. ──
  function spanWalk(n, lo, hi, text, file, spans) {
    const surf = n.leanNode ? surface(n.leanNode) : null;
    let loc = surf ? locate(text, lo, hi, surf) : null;
    const clo = loc ? loc.start : lo, chi = loc ? loc.end : hi;
    (n.children || []).forEach((c) => spanWalk(c, clo, chi, text, file, spans));
    if (!loc && n.leanNode && (n.status === 'leaf' || n.status === 'match') && (n.children || []).length) {
      let a = Infinity, b = -Infinity;
      for (const c of n.children) { const cs = c.fol && spans[c.fol]; if (cs && cs.start != null) { if (cs.start < a) a = cs.start; if (cs.end > b) b = cs.end; } }
      if (b > a) loc = { start: a, end: b };
    }
    const notok = n.status === 'mismatch' || n.status === 'unmapped';
    if (loc && n.fol) spans[n.fol] = { file, start: loc.start, end: loc.end, v: notok ? 'notok' : 'ok' };
    else if (n.fol && notok) spans[n.fol] = { file, start: lo, end: hi, v: 'notok' };
  }

  const bad = (node) => { let s = 0; (function w(n) { if (!n) return; if (n.status === 'mismatch' || n.status === 'unmapped' || n.status === 'skipped') s++; (n.children || []).forEach(w); })(node); return s; };
  const good = (node) => { let s = 0; (function w(n) { if (!n) return; if (n.status === 'leaf' || n.status === 'match' || n.status === 'typed') s++; (n.children || []).forEach(w); })(node); return s; };
  const firstBad = (node) => { let h = null; (function w(n) { if (h || !n) return; if (n.status === 'mismatch' || n.status === 'unmapped' || n.status === 'skipped') { h = n; return; } (n.children || []).forEach(w); })(node); return h; };
  const nlText = (b) => { const ps = C.pieces(b); return ps.length ? chars.slice(ps[0].start, ps[ps.length - 1].end).replace(/\s+/g, ' ').trim() : ''; };
  const labelPath = (b) => b && b.label ? b.label.join('.') : '';

  // CANDIDATE PROPS: the props with a locatable source region, deduped by region —
  // the set a step can be faithful to AND the set the LLM routes among (same set, so
  // the routed prop always has a span to display). Drops the extraction's hygienic
  // noise (`a`,`b`,`i`,… with null regions) that can neither be shown nor meaningfully
  // matched.
  const cands = (() => { const seen = new Set(), out = [];
    for (const p of props) { if (!p.region) continue; const k = p.file + ':' + p.region[0] + '-' + p.region[1];
      if (seen.has(k)) continue; seen.add(k); out.push(p); } return out; })();
  const regionText = (p) => p.text.slice(p.region[0], p.region[1]).replace(/\s+/g, ' ').trim();
  const safeAlign = (step, p) => { try { return A.align(step, p.node); } catch (_) { return null; } };

  // ── match each step, allocate spans, collect findings ──
  const spans = {};
  const children = [];
  const findings = [];
  for (const step of steps) {
    let hit = null, hitRes = null, best = null, bestGood = -1;
    for (const f of cands) {
      let res; try { res = A.align(step, f.node); } catch (_) { continue; }
      if (bad(res) === 0) { hit = f; hitRes = res; break; }
      const g = good(res); if (g > bestGood) { bestGood = g; best = f; }
    }
    const faithful = !!hit;
    // FAITHFUL: the clean-matching prop. UNFAITHFUL: ask the LLM which prop this step
    // is INTENDED to match (routing only — the verdict is already unfaithful); fall
    // back to the heuristic `best` (max matched nodes) if routing is off or fails.
    let chosen, res;
    if (faithful) { chosen = hit; res = hitRes; }
    else {
      let pick = null;
      if (llmEnabled && cands.length) {
        const idx = routeStepToProp(nlText(step), cands.map(regionText), { model: 'claude-sonnet-5' });
        if (idx != null) pick = cands[idx];
      }
      chosen = pick || best || cands[0] || null;
      res = chosen ? safeAlign(step, chosen) : null;
    }
    if (chosen && res) {
      const [lo, hi] = chosen.region || [0, 0];
      if (chosen.region) spanWalk(res, lo, hi, chosen.text, chosen.file, spans);
      // tag the step's own box with the overall verdict (so the tree badge shows it)
      res.proofStep = step.id; res.verdict = faithful ? 'faithful' : 'unfaithful'; res.witness = chosen.tag;
      children.push(res);
      const fb = faithful ? null : firstBad(res);
      // GUARANTEE every step maps to SOMEWHERE — the Lean proposition it was matched
      // (faithful) or compared against (its CLOSEST near-miss, unfaithful). The
      // step-level span is ALWAYS colored by the step's own verdict, so a faithful
      // step reads ok even when its top node is a prefix-form relation that didn't
      // surface-locate (it would otherwise map to nothing), and an unfaithful step
      // reads notok even when its outer shape (e.g. the `=`) matched and a child is
      // what diverged (it would otherwise inherit the child's green). Finer per-node
      // spans from spanWalk stay as children for drill-down.
      if (chosen.region) {
        if (faithful) {
          // keep a precise located span if the walk produced one; else the whole prop.
          if (!spans[step.id] || spans[step.id].start == null) spans[step.id] = { file: chosen.file, start: lo, end: hi };
          spans[step.id].v = 'ok'; spans[step.id].witness = chosen.tag;
        } else {
          // the WHOLE closest-prop region — so you SEE the candidate it compared to
          // (not a degenerate sub-token), flagged notok with the divergence reason.
          spans[step.id] = { file: chosen.file, start: lo, end: hi, v: 'notok',
            why: fb ? `closest: ${chosen.tag} — diverges at ${labelPath(C.find(root, fb.fol))} (${fb.note})` : `no clean match; closest ${chosen.tag}`,
            cmp: chosen.text.slice(lo, hi).replace(/\s+/g, ' ').trim(), path: labelPath(step) };
        }
      }
      if (!faithful) {
        const line = chosen.region ? chosen.text.slice(0, chosen.region[0]).split('\n').length : null;
        findings.push({ fol: step.id, path: labelPath(step), nl: nlText(step) || '(implicit)',
          lean: chosen.text && chosen.region ? chosen.text.slice(chosen.region[0], chosen.region[1]).replace(/\s+/g, ' ').trim() : chosen.text,
          leanLoc: chosen.file + (line ? ':' + line : ''),
          message: fb ? `closest: ${chosen.tag} — diverges at ${labelPath(C.find(root, fb.fol))} vs Lean (${fb.note})` : `no clean match; closest ${chosen.tag}` });
      }
    } else {
      findings.push({ fol: step.id, path: labelPath(step), nl: nlText(step) || '(implicit)', lean: '', leanLoc: '', message: 'no structurally-matching Lean proposition found' });
      children.push({ fol: step.id, status: 'unmapped', note: 'no match', children: [] });
    }
  }

  const alignment = { fol: proofBox.id, lean: null, leanNode: null, status: 'match', note: '', children };
  const file0 = assocs[0] ? leanRel(assocs[0]) : '';
  return { ok: true, alignment, findings, spans, leanRegions: [],
    leanDecl: assocs.map((a) => a.decl.split('.').pop()).join(' + '),
    leanFile: file0, leanLine: null,
    leanSource: '', leanElaborated: '' };
}
