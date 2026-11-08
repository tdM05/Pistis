// align_driver — ties the pieces together: given a FOL definition/theorem box id,
// extract its Lean decl, normalize, align, and return {alignment, findings}.
//
// Pure except for extract() (which shells to lean, cached). Shared by the CLI
// (inspect.js --align) and the server (/align endpoint for the UI).
import { normalize, peelBinders } from './lean_normalize.js';
import { makeAligner } from './align.js';
import { extract } from './lean_extract/extract.js';

// Align one FOL box (a definition or theorem) against its Lean decl.
//   core    : makeCore(schema) result
//   root    : the annotation ROOT
//   box     : the FOL box (must be in dict.decls)
//   chars   : the global CHARS string (for symbol slugs)
//   dict    : lean_dict.json  ({decls, symbols})
// Returns { ok, reason?, alignment?, findings?, leanDecl? }.
export function alignBox({ core, root, box, chars, dict }) {
  const C = core;
  const assoc = dict.decls && dict.decls[box.id];
  if (!assoc) return { ok: false, reason: `no Lean decl associated with ${box.id} (add it to lean_dict.json → decls)` };
  let raw; try { raw = extract({ decl: assoc.decl, srcFile: assoc.src }); }
  catch (e) { return { ok: false, reason: 'lean extract failed: ' + e.message }; }

  const concrete = C.labelConcrete(box.label);
  const symText = (x) => { const ps = C.pieces(x); if (!ps.length) return '∅'; return chars.slice(ps[0].start, ps[0].end).replace(/\s+/g, ' ').trim().replace(/ /g, '_'); };
  const A = makeAligner(C, dict.symbols || {}, symText);

  // Lean side: a `def` elaborates to `fun <inputs> => body`. Peel the lam-binders
  // (the inputs) to reach the body (which the FOL `body` slot aligns against).
  // For a theorem the value is a proof; we align the TYPE (the statement) instead.
  const normVal = raw.value && raw.value.kind ? normalize(raw.value) : null;
  const normType = normalize(raw.type);

  if (concrete === 'definition') {
    // peel the input lam-binders off the value to get the defining body
    const { binders, body } = peelBinders(normVal || {});
    const lamInputs = binders.filter((b) => b.kind === 'lam');
    let leanBody = normVal; for (let i = 0; i < lamInputs.length; i++) leanBody = leanBody.body;
    // the FOL body box = the definition's `body` child
    const bodyBox = (box.children || []).find((k) => k.label && k.label[0] === 'body');
    if (!bodyBox) return { ok: false, reason: 'definition has no body slot to align' };
    const alignment = A.alignNode(bodyBox, leanBody);
    return finish(alignment, assoc, lamInputs);
  }
  // theorem / formula: align the box against the Lean TYPE (the statement)
  const alignment = A.alignNode(box, normType);
  return finish(alignment, assoc, []);

  function finish(alignment, assoc, lamInputs) {
    const findings = [];
    (function collect(n) {
      if (n.status === 'mismatch' || n.status === 'unmapped') findings.push({ fol: n.fol, lean: n.lean, status: n.status, note: n.note });
      (n.children || []).forEach(collect);
    })(alignment);
    return { ok: true, alignment, findings, leanDecl: assoc.decl, leanInputs: lamInputs.map((b) => ({ binder: b.binder, info: b.info })) };
  }
}
