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

const SEG_DIR = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');   // pdf_direct_segment/

// Align one FOL box (a definition or theorem) against its Lean decl.
//   core    : makeCore(schema) result
//   root    : the annotation ROOT
//   box     : the FOL box (must be in dict.decls)
//   chars   : the global CHARS string (for symbol slugs)
//   dict    : lean_dict.json  ({decls, symbols})
// Returns { ok, reason?, alignment?, findings?, leanDecl? }.
export function alignBox({ core, root, box, chars, dict }) {
  const C = core;
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
  const typeBinders = peelTypeBinders(raw.type).map((b) => ({ binder: b.binder, info: b.info, dom: b.dom, typeConsts: constNames(b.dom || {}) }));
  const A = makeAligner(C, dict.symbols || {}, symText, { binders: typeBinders, tuples: dict.tuples || {} });

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
    const children = [];
    children.push(alignName(slot('name'), assoc.decl));
    children.push(alignInputs(slot('inputs'), typeBinders));
    children.push(alignConditions(slot('conditions'), typeBinders));
    children.push(labelNode(bodyBox, A.align(bodyBox, leanBody), 'body'));

    const alignment = { fol: box.id, lean: null, leanNode: null, status: 'match', note: '', children };
    return finish(alignment, assoc, lamInputs, { leanBody, typeBinders });
  }
  // theorem / formula: align the box against the Lean TYPE (the statement)
  const alignment = A.align(box, normType);
  return finish(alignment, assoc, [], { leanBody: normType, typeBinders });

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
  // classify a Lean type-binder: a CONSTRAINT (hypothesis — maps to a condition) if
  // it is an instance arg `[…]` or its domain is a Prop (a relation, e.g. a `Fintype`
  // instance or `h : T ⊆ S`); otherwise an OBJECT (data — maps to an input).
  function isConstraintBinder(tb) {
    const PROP_SHAPES = new Set(['and', 'or', 'not', 'iff', 'eq', 'mem', 'arrow', 'forall']);
    return tb.info === 'instImplicit' || (tb.dom && PROP_SHAPES.has(tb.dom.t));
  }
  // inputs ↔ OBJECT binders, POSITIONALLY (Nth input ↔ Nth object binder). No name
  // matching: the author writes the inputs in the same order as the Lean binders. A
  // positional count mismatch (extra input, or an object binder with no input) is a
  // finding.
  function alignInputs(inputsBox, tbinders) {
    if (!inputsBox) return { fol: null, lean: null, leanNode: null, status: 'match', note: 'no inputs slot', slot: 'inputs', children: [] };
    const invars = (inputsBox.children || []).filter((c) => C.isVariable(c));
    const objs = tbinders.filter((tb) => !isConstraintBinder(tb));
    const kids = []; const n = Math.max(invars.length, objs.length);
    for (let i = 0; i < n; i++) {
      const v = invars[i], tb = objs[i];
      if (v && tb) kids.push({ fol: v.id, lean: 'binder ' + tb.binder, leanNode: { t: 'var', name: tb.binder }, status: 'leaf', note: `input #${i + 1} ↔ binder ${tb.binder}`, children: [] });
      else if (v) kids.push({ fol: v.id, lean: null, leanNode: null, status: 'unmapped', note: `input #${i + 1} '${symText(v)}' has no Lean object binder at this position`, children: [] });
      else kids.push({ fol: null, lean: 'binder ' + tb.binder, leanNode: { t: 'var', name: tb.binder }, status: 'unmapped', note: `Lean object binder #${i + 1} '${tb.binder}' has no input at this position`, children: [] });
    }
    const bad = kids.some((k) => k.status !== 'leaf');
    return { fol: inputsBox.id, lean: null, leanNode: null, status: bad ? 'mismatch' : 'match', note: '', slot: 'inputs', children: kids };
  }
  // conditions ↔ CONSTRAINT binders, POSITIONALLY (Nth condition ↔ Nth constraint
  // binder). Each condition then aligns against that binder's TYPE as a formula.
  // Count mismatch is a finding.
  function alignConditions(condsBox, tbinders) {
    if (!condsBox) return { fol: null, lean: null, leanNode: null, status: 'match', note: 'no conditions slot', slot: 'conditions', children: [] };
    const conds = (condsBox.children || []).filter((c) => C.isFormulaish(c));
    const cons = tbinders.filter((tb) => isConstraintBinder(tb));
    const kids = []; const n = Math.max(conds.length, cons.length);
    for (let i = 0; i < n; i++) {
      const cond = conds[i], tb = cons[i];
      if (cond && tb) kids.push({ fol: cond.id, lean: 'type of ' + tb.binder, leanNode: tb.dom || null, status: 'leaf', note: `condition #${i + 1} ↔ type of binder ${tb.binder}`, children: [] });
      else if (cond) kids.push({ fol: cond.id, lean: null, leanNode: null, status: 'unmapped', note: `condition #${i + 1} has no Lean constraint binder at this position`, children: [] });
      else kids.push({ fol: null, lean: 'type of ' + tb.binder, leanNode: tb.dom || null, status: 'unmapped', note: `Lean constraint binder #${i + 1} '${tb.binder}' has no condition at this position`, children: [] });
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
    let text = '', fileField = '', leanSource = '', leanLine = null;
    try {
      const abs = path.join(SEG_DIR, deriveLeanRel(assoc));
      text = readFileSync(abs, 'utf8');
      fileField = deriveLeanRel(assoc);
      const nameLeaf = assoc.decl.split('.').pop();
      const declAt = text.indexOf('def ' + nameLeaf);
      const asgn = declAt >= 0 ? text.indexOf(':=', declAt) : text.indexOf(':=');
      // region boundaries within the source:
      //   [sigLo, sigHi)  = the signature (name + binders + result type), before :=
      //   [bodyLo, bodyHi)= the body, after :=
      const sigLo = declAt >= 0 ? declAt : 0;
      const sigHi = asgn >= 0 ? asgn : (declAt >= 0 ? text.indexOf('\n', declAt) : 0);
      let bodyLo = asgn >= 0 ? asgn + 2 : 0;
      let bodyHi = text.indexOf('\n\n', bodyLo); if (bodyHi < 0) bodyHi = text.length;
      const tnl = text.indexOf('\ntheorem', bodyLo); if (tnl >= 0 && tnl < bodyHi) bodyHi = tnl;
      // 1-based line of the decl, and the verbatim source of the whole decl, for display
      if (declAt >= 0) { leanLine = text.slice(0, declAt).split('\n').length; leanSource = text.slice(sigLo, bodyHi).trim(); }
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
        let mySpan = null;
        const surf = n.leanNode ? surface(n.leanNode) : null;
        const loc = surf ? locate(text, lo, hi, surf) : null;
        if (loc) { mySpan = loc; if (n.fol) spans[n.fol] = { file: fileField, start: loc.start, end: loc.end }; }
        else if (n.fol && n.leanNode) spans[n.fol] = { file: fileField, start: lo, end: hi, approx: true };
        n.nl = nlText(n.fol);
        n.leanText = loc ? text.slice(loc.start, loc.end).replace(/\s+/g, ' ').trim() : (n.leanNode ? pretty(n.leanNode) : '');
        const clo = mySpan ? mySpan.start : lo, chi = mySpan ? mySpan.end : hi;
        (n.children || []).forEach((c) => walk(c, clo, chi, mySlot));
      };
      walk(alignment, bodyLo, bodyHi, null);
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
        findings.push({
          fol: n.fol,
          path: labelPath(n.fol),
          nl: n.nl || '(implicit)',
          lean: n.leanText || n.lean,
          leanLoc: sp ? `${sp.file}:${sp.start}-${sp.end}` : (fileField ? `${fileField}${leanLine ? ':' + leanLine : ''}` : ''),
          message: humanFinding(n),
        });
      }
      (n.children || []).forEach(collect);
    })(alignment);
    return {
      ok: true, alignment, findings, spans,
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
    if (/INCONSISTENT/.test(n.note)) {
      const m = n.note.match(/variable (\S+) maps to INCONSISTENT Lean terms \(([^)]+)\)/);
      const v = m ? m[1] : '?';
      const parts = m ? m[2].split(', ').map((x) => x.replace(/^v:|^c:|^app:c:|^app:|^lit:|^tuple:/, '')) : [];
      return `variable ${v} maps to multiple Lean terms {${parts.join(', ')}} — must denote one thing`;
    }
    const single = n.note.match(/single (\w+)/);               // ∧-vs-non-∧ (body halt)
    if (single) return `this ${kind} has no Lean counterpart of the same shape — Lean here is a ${leanShapeName(single[1])} — structures differ`;
    const vs = n.note.match(/FOL (\w+) vs Lean (\w+)/);         // connective mismatch
    if (vs) return `this ${kind} is a ${vs[1]}, Lean counterpart is a ${leanShapeName(vs[2])} — structures differ`;
    if (/no Lean binder/.test(n.note) || /no Lean binder-type/.test(n.note)) return `${n.note} (present in NL, absent in Lean)`;
    if (/Lean binds|Lean defines/.test(n.note)) return n.note;  // Lean-side extra (fol is null)
    if (/no .*counterpart/.test(n.note)) return n.note;
    if (/another ∀/.test(n.note)) return `NL binds one variable, Lean binds two`;
    return n.note;
  }
  // readable name for a Lean structural kind.
  function leanShapeName(t) {
    return ({ forall: '∀ (forall)', exists: '∃ (exists)', arrow: '→ (implication)', and: '∧ (and)', or: '∨ (or)', not: '¬ (not)', eq: '= (equality)', mem: '∈ (membership)', app: 'application' })[t] || t;
  }
  // the .lean file path as stored in box.lean.spans (relative to pdf_direct_segment/,
  // i.e. "lean/MaxSupportKernel.lean") — matches how the Lean pane references files.
  function deriveLeanRel(assoc) {
    const base = assoc.src.split('/').pop();   // MaxSupportKernel.lean
    return 'lean/' + base;
  }
}
