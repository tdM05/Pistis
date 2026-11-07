// ─────────────────────────────────────────────────────────────────────────────
// core.js — pure label/validation logic, NO DOM. Shared by ui/app.js (browser,
// via <script type="module">) and tools/*.js (node, via a tiny loader). All rules
// come from schema.json; this file is only the algorithms over them.
//
// Usage: const C = makeCore(schema);  then C.boxIssues(box, {root, chars}), etc.
// Tree-walking helpers (walk/find/parentOf) take the root explicitly so there is
// no hidden global state.
// ─────────────────────────────────────────────────────────────────────────────

export function makeCore(schema) {
  const { ISA, HASA, ROOT_SLOTS, LABEL_SHORT, DERIVED_SYM, CONDITIONS, COUNTED_SLOT } = schema;
  const COMMENTARY_ANYWHERE = schema.COMMENTARY_ANYWHERE !== false;

  // ── tree helpers (root passed in) ──
  const walk = (n, fn, d = 0) => { fn(n, d); (n.children || []).forEach((c) => walk(c, fn, d + 1)); };
  const find = (root, id) => { let f = null; walk(root, (n) => { if (n.id === id) f = n; }); return f; };
  const parentOf = (root, id) => { let p = null; walk(root, (n) => { if ((n.children || []).some((c) => c.id === id)) p = n; }); return p; };
  const pieces = (b) => b.pieces || [];
  const regionLen = (b) => pieces(b).reduce((t, p) => t + (p.end - p.start), 0);

  // ── label classification ──
  const isAbstract = (l) => l in ISA;
  const isComposite = (l) => l in HASA;
  const isLeafLabel = (l) => !isAbstract(l) && !isComposite(l);          // has-a base
  const labelConcrete = (path) => (path && path.length ? path[path.length - 1] : null);

  const ISA_PARENT = {}; for (const k in ISA) for (const c of ISA[k]) ISA_PARENT[c] = k;
  const canonPath = (label) => { const p = [label]; let x = label; while (ISA_PARENT[x]) { x = ISA_PARENT[x]; p.unshift(x); } return p; };

  // is label l the slot, or an is-a subtype of it (descend)?
  const labelSubtypes = (l, slot) => { if (l === slot) return true; const k = ISA[l]; return k ? k.some((c) => labelSubtypes(c, slot)) : false; };
  // a child counts as `slot` if its CONCRETE label IS-A slot (slot on its ancestry)
  const childCountsAs = (child, slot) => { const c = labelConcrete(child.label); if (!c) return false; return canonPath(c).includes(slot) || labelSubtypes(c, slot); };

  // all full paths of CONCRETE labels reachable by refining `slot`
  const pathsUnder = (slot, prefix) => {
    let base = prefix && prefix.length ? prefix : [];
    if (!base.length) { const c = canonPath(slot); if (c[0] === 'symbol') base = c.slice(0, -1); }
    const p = [...base, slot];
    if (!isAbstract(slot)) return [p];
    return ISA[slot].flatMap((c) => pathsUnder(c, p));
  };
  // has-a slots of a box = union of HASA over every label in its is-a path, + commentary on composites
  const hasaSlotsOf = (box) => {
    const out = []; let composite = false;
    for (const l of (box.label || [])) { if (l in HASA) composite = true; (HASA[l] || []).forEach((s) => { if (!out.includes(s)) out.push(s); }); }
    if (composite && COMMENTARY_ANYWHERE && !out.includes('commentary')) out.push('commentary');
    return out;
  };
  // valid label-paths for a box given its PARENT box (null parent/root → ROOT_SLOTS)
  const allowedLabelPaths = (root, parentBox) => {
    const atTop = !parentBox || parentBox === root || parentBox.id === 'root';
    const slots = atTop ? ROOT_SLOTS : (parentBox.label ? hasaSlotsOf(parentBox) : null);
    if (!slots) return null;
    return slots.flatMap((s) => pathsUnder(s, []));
  };

  // ── display ──
  const lblShort = (l) => LABEL_SHORT[l] || l;
  const derivedSymbol = (root, box) => {
    const c = labelConcrete(box.label); const map = c && DERIVED_SYM[c]; if (!map) return null;
    const par = parentOf(root, box.id); const pc = par && par.label ? labelConcrete(par.label) : null; const sym = pc && map[pc];
    return sym ? { sym, reason: `${c} inside ${pc} ⇒ ${sym}` } : null;
  };
  const labelTag = (root, box) => {
    const path = box && box.label; if (!path || !path.length) return '';
    const a = lblShort(path[0]); if (path.length === 1) return a;
    const ds = box.id ? derivedSymbol(root, box) : null;
    return a + '.' + (ds ? ds.sym : lblShort(path[path.length - 1]));
  };

  // ── geometry (char intervals) ──
  const mergeIntervals = (ivs) => {
    const s = ivs.slice().sort((a, b) => a.start - b.start); const out = [];
    for (const iv of s) { const last = out[out.length - 1]; if (last && iv.start <= last.end) last.end = Math.max(last.end, iv.end); else out.push({ start: iv.start, end: iv.end }); }
    return out;
  };
  // coverage of a box by its children's pieces: {covered,total,gaps}
  const coverageOf = (box) => {
    const own = mergeIntervals(pieces(box)); const total = own.reduce((t, p) => t + (p.end - p.start), 0);
    const kid = mergeIntervals((box.children || []).flatMap((c) => pieces(c)));
    let covered = 0; const gaps = [];
    for (const p of own) {
      let cur = p.start;
      for (const k of kid) { if (k.end <= cur || k.start >= p.end) continue; const a = Math.max(k.start, cur), b = Math.min(k.end, p.end); if (a > cur) gaps.push({ start: cur, end: a }); covered += Math.max(0, b - a); cur = Math.max(cur, b); }
      if (cur < p.end) gaps.push({ start: cur, end: p.end });
    }
    return { covered, total, gaps };
  };

  // ── validation: issues for ONE box (not recursive) ──
  const boxIssues = (box) => {
    const out = [];
    if (!box.label || !box.label.length) { out.push('unlabelled'); return out; }
    const concrete = labelConcrete(box.label);
    if (isAbstract(concrete)) out.push('incomplete label (ends abstract)');
    for (const c of (CONDITIONS[concrete] || [])) {
      const n = (box.children || []).filter((ch) => childCountsAs(ch, c.slot)).length;
      if (n < c.min) out.push(`needs ${c.min === c.max ? c.min : c.min + '+'} ${c.slot} (has ${n})`);
      else if (c.max != null && n > c.max) out.push(`too many ${c.slot} (${n}, max ${c.max})`);
    }
    const slots = hasaSlotsOf(box);
    for (const ch of (box.children || [])) { const head = ch.label && ch.label[0]; if (head && !slots.some((s) => labelSubtypes(head, s))) out.push(`child “${head}” not allowed here`); }
    const cslot = COUNTED_SLOT[concrete];
    if (cslot) { const have = (box.children || []).filter((ch) => childCountsAs(ch, cslot)).length;
      if (box.count == null) out.push(`specify number of ${cslot}s (have ${have})`);
      else if (box.count !== have) out.push(`declared ${box.count} ${cslot}${box.count === 1 ? '' : 's'}, have ${have}`); }
    if (box.children && box.children.length && !isLeafLabel(concrete)) {
      const cov = coverageOf(box); if (cov.gaps.length) { const pct = cov.total ? Math.round(100 * cov.covered / cov.total) : 100; out.push(`children cover ${pct}% (${cov.gaps.length} gap${cov.gaps.length > 1 ? 's' : ''})`); }
    }
    return out;
  };
  const allIssues = (root) => { const out = []; walk(root, (n) => { if (n === root) return; const iss = boxIssues(n); if (iss.length) out.push({ id: n.id, box: n, issues: iss }); }); return out; };

  // ── variable naming / scope ──
  // A VARIABLE's identity is its name (v0, v1, …), matched within its SCOPE unit.
  // Scope unit = nearest enclosing definition / theorem; else the top-level box
  // under root. (Links are NOT used for variable coreference; same name = same var.)
  const SCOPE_LABELS = new Set(['definition', 'theorem']);
  const scopeOf = (root, box) => {
    let x = box, last = box;
    while (x && x !== root) { const c = labelConcrete(x.label); if (SCOPE_LABELS.has(c)) return x; last = x; x = parentOf(root, x.id); }
    // no def/theorem ancestor → the top-level box (direct child of root) it sits under
    return last;
  };
  // both a `variable` TERM (used occurrence) and a `variable-symbol` (the bound
  // symbol after ∀/∃) carry variable identity and share the var-name namespace,
  // so coreference across binder + uses works (∀x. P(x) → both x are the same name).
  const isVariable = (box) => { const c = labelConcrete(box.label); return c === 'variable' || c === 'variable-symbol'; };
  // every variable name currently used inside a scope (for freshness / coref view)
  const varsInScope = (root, scope) => { const names = {}; walk(scope, (n) => { if (isVariable(n) && n.var != null) names[n.var] = (names[n.var] || 0) + 1; }); return names; };
  // next fresh v{N} not used in the scope
  const freshVarName = (root, scope) => { const used = varsInScope(root, scope); let i = 0; while (used['v' + i]) i++; return 'v' + i; };

  // ── FOL rendering (Bilaniuk Def 5.2/5.3, extended with ∧∨∃↔ abbreviations) ──
  // Render a box to a FOL formula as a flat TOKEN LIST (not just a string), so
  // callers can render it richly (color by kind, subscripts) or flatten it to
  // text. `symText(box)` returns a symbol box's printed name (highlighted span
  // text, slugified) — supplied by the caller since core has no text source.
  // Collects the signature (relations/functions/constants with arities) and free
  // variables into `sig` as a side effect.
  //
  // Token = {t, s} where t ∈ var|rel|fn|con|logic|punct|sp and s is its text.
  //  var  — variable name (vᵢ)           rel  — relation symbol
  //  fn   — function symbol              con  — constant symbol
  //  logic— ∀ ∃ ¬ ∧ ∨ → ↔ =             punct— parens / commas
  //  sp   — a single space               .impl=true marks an implicit (∅) symbol.
  // Returns {str, tokens, sig}: str = tokens joined verbatim (back-compat).
  const INFIX = { conjunction: '∧', disjunction: '∨', implication: '→' };
  function toFOL(root, box, symText, sig) {
    sig = sig || { rel: {}, fn: {}, con: {}, vars: new Set() };
    const V = (s) => ({ t: 'var', s }); const REL = (s, impl) => ({ t: 'rel', s, impl });
    const FN = (s, impl) => ({ t: 'fn', s, impl }); const CON = (s, impl) => ({ t: 'con', s, impl });
    const L = (s) => ({ t: 'logic', s }); const P = (s) => ({ t: 'punct', s }); const SP = { t: 'sp', s: ' ' };
    const Q = (s) => ({ t: 'logic', s });
    // flatten token-arrays, inserting `sep` (a token array) between them
    const join = (arrs, sep) => { const o = []; arrs.forEach((a, i) => { if (i) o.push(...sep); o.push(...a); }); return o; };
    const rec = (b) => {
      const kids = (b.children || []).filter((c) => labelConcrete(c.label) !== 'commentary');
      const c = labelConcrete(b.label);
      const symOf = (x) => (x.implicit ? '∅' : symText(x));
      switch (c) {
        case 'variable': case 'variable-symbol': { const v = b.var || '?'; sig.vars.add(v); return [V(v)]; }
        case 'constant': { const s = symOf(b); sig.con[s] = 0; return [CON(s, b.implicit)]; }
        case 'external-citation': case 'implicit-external-reference': { const s = symOf(b); sig.con[s] = 0; return [CON(s, b.implicit)]; }
        case 'function-application': {
          const fsym = kids.find((k) => labelConcrete(k.label) === 'function-symbol');
          const terms = kids.filter((k) => k !== fsym);
          const f = fsym ? symOf(fsym) : '∅'; sig.fn[f] = terms.length;
          return [FN(f, fsym ? fsym.implicit : true), P('('), ...join(terms.map(rec), [P(','), SP]), P(')')];
        }
        case 'relation': {
          const rsym = kids.find((k) => labelConcrete(k.label) === 'relation-symbol');
          const terms = kids.filter((k) => k !== rsym);
          const r = rsym ? symOf(rsym) : '∅'; sig.rel[r] = terms.length;
          return [REL(r, rsym ? rsym.implicit : true), P('('), ...join(terms.map(rec), [P(','), SP]), P(')')];
        }
        case 'equality': { const terms = kids.filter((k) => labelConcrete(k.label) !== 'equality-symbol'); return [...rec(terms[0]), SP, L('='), SP, ...rec(terms[1])]; }
        case 'negation': { const f = kids.find((k) => isFormulaish(k)); return [L('¬'), ...(f ? rec(f) : [P('?')])]; }
        case 'conjunction': case 'disjunction': case 'implication': {
          const fs = kids.filter((k) => isFormulaish(k)); return [P('('), ...join(fs.map(rec), [SP, L(INFIX[c]), SP]), P(')')];
        }
        case 'universal': case 'existential': {
          const q = c === 'universal' ? '∀' : '∃';
          const vb = kids.find((k) => isVariable(k)); const body = kids.find((k) => isFormulaish(k));
          const v = vb ? (vb.var || '?') : '?'; sig.vars.add(v);
          return [Q(q), V(v), SP, ...(body ? rec(body) : [P('?')])];
        }
        case 'theorem': { const f = kids.find((k) => isFormulaish(k)); return f ? rec(f) : [P('?')]; }
        case 'body': case 'formula': case 'atomic-formula': case 'compound-formula': case 'quantified': case 'connective': case 'atomic-term': case 'composite-term': case 'term': {
          // abstract wrapper: should have exactly one concrete child to render
          const only = kids[0]; return only ? rec(only) : [P('?')];
        }
        case 'definition': {
          const head = (k) => k.label && k.label[0];   // name/inputs/conditions/body are top-label slots
          const name = kids.find((k) => head(k) === 'name');
          const inputs = kids.find((k) => head(k) === 'inputs');
          const conds = kids.find((k) => head(k) === 'conditions');
          const bodyB = kids.find((k) => head(k) === 'body');
          const nm = name ? symText(name) : '∅';
          const ivars = inputs ? (inputs.children || []).filter(isVariable).map((v) => { sig.vars.add(v.var); return v.var; }) : [];
          sig.rel[nm] = ivars.length;   // the definiendum = a new relation symbol
          const lhs = [REL(nm, name ? name.implicit : true), P('('), ...join(ivars.map((v) => [V(v)]), [P(','), SP]), P(')')];
          const rhs = bodyB ? rec(bodyB) : [P('?')];
          const condArr = conds ? (conds.children || []).filter(isFormulaish).map(rec) : [];
          const bicond = [...lhs, SP, L('↔'), SP, ...rhs];
          const body2 = condArr.length
            ? [P('('), ...join(condArr, [SP, L('∧'), SP]), P(')'), SP, L('→'), SP, P('('), ...bicond, P(')')]
            : bicond;
          const pre = []; ivars.forEach((v) => pre.push(Q('∀'), V(v)));
          return ivars.length ? [...pre, SP, ...body2] : body2;
        }
        default: { const only = kids[0]; return only ? rec(only) : [CON(symOf(b) || '?', b.implicit)]; }
      }
    };
    const tokens = rec(box);
    const str = tokens.map((t) => t.s).join('');
    return { str, tokens, sig };
  }
  const isFormulaish = (b) => { const c = labelConcrete(b.label); return c && (c === 'formula' || canonPath(c).includes('formula') || c === 'body'); };
  // can this box be rendered as a FOL formula at all? (vs commentary / a bare
  // symbol / an organizer — those have their own view in folView)
  const isFolable = (b) => { const c = labelConcrete(b && b.label); return !!c && (c === 'definition' || c === 'theorem' || isFormulaish(b) || canonPath(c).includes('term') || canonPath(c).includes('formula')); };
  // does `box` or any descendant have a structural issue? (a half-labelled
  // subtree can't render a meaningful formula — folView suppresses it)
  const subtreeHasIssue = (box) => { let bad = false; walk(box, (n) => { if (boxIssues(n).length) bad = true; }); return bad; };

  // ── FOL VIEW: box-kind dispatch, shared by UI + CLI ──
  // Returns a view descriptor describing how to present `box` in the FOL tab.
  // Every part is {label, items:[{tokens,id?}]}: a single formula/term is one
  // part with one item; a LIST slot (conditions, inputs, …) is one part whose
  // items are its members — NOT fused with ∧. Kinds:
  //   {kind:'none',  reason}                           commentary / nothing
  //   {kind:'error', issues:[{id,tag,msgs}]}            subtree has issues → suppress
  //   {kind:'formula', tokens, sig}                     a single formula/term
  //   {kind:'list',  title, items:[{tokens,id}], sig}   a slot's members, listed
  //   {kind:'parts', title, parts:[{label,items}], sig} a definition, broken out
  //   {kind:'group', title, parts:[{label,id,view}]}    an organizer's members
  // `symText(box)` supplies printed symbol names (see toFOL).
  function folView(root, box, symText) {
    const c = labelConcrete(box && box.label);
    if (!box || !box.label || !box.label.length) return { kind: 'none', reason: 'unlabelled — no FOL' };
    if (c === 'commentary') return { kind: 'none', reason: 'commentary — no formula' };
    const kidsOf = (b) => (b.children || []).filter((k) => labelConcrete(k.label) !== 'commentary');
    // organizer: list each member's own FOL view (recurse one level)
    if (c === 'organizer-section') {
      const parts = kidsOf(box).map((k) => ({ label: k.label ? labelTag(root, k) : k.id, id: k.id, view: folView(root, k, symText) }));
      return { kind: 'group', title: 'organizer — ' + parts.length + ' member(s)', parts };
    }
    // suppress on errors anywhere in the subtree we'd render
    const issues = [];
    walk(box, (n) => { const m = boxIssues(n); if (m.length) issues.push({ id: n.id, tag: n.label ? labelTag(root, n) : 'unlabelled', msgs: m }); });
    if (issues.length) return { kind: 'error', issues };
    const sig = { rel: {}, fn: {}, con: {}, vars: new Set() };
    // definition: show each slot broken out (conditions kept as a LIST). No
    // synthesized "whole" biconditional — the parts ARE the content.
    if (c === 'definition') {
      const head = (k) => k.label && k.label[0];
      const kids = kidsOf(box);
      const name = kids.find((k) => head(k) === 'name');
      const inputs = kids.find((k) => head(k) === 'inputs');
      const conds = kids.find((k) => head(k) === 'conditions');
      const bodyB = kids.find((k) => head(k) === 'body');
      const parts = [];
      const nm = name ? symText(name) : '∅';
      const ivs = inputs ? kidsOf(inputs).filter(isVariable) : [];
      ivs.forEach((v) => sig.vars.add(v.var));
      sig.rel[nm] = ivs.length;   // definiendum = a new relation symbol
      parts.push({ label: 'name', items: [{ tokens: [{ t: 'rel', s: nm, impl: name ? name.implicit : true }], id: name && name.id }] });
      if (inputs) parts.push({ label: 'inputs', items: ivs.length ? ivs.map((v) => ({ tokens: [{ t: 'var', s: v.var || '?' }], id: v.id })) : [{ tokens: [{ t: 'punct', s: '— none' }] }] });
      if (conds) { const cfs = kidsOf(conds); parts.push({ label: 'conditions', items: cfs.length ? cfs.map((f) => ({ tokens: toFOL(root, f, symText, sig).tokens, id: f.id })) : [{ tokens: [{ t: 'punct', s: '— none' }] }] }); }
      if (bodyB) parts.push({ label: 'body', items: [{ tokens: toFOL(root, bodyB, symText, sig).tokens, id: bodyB.id }] });
      return { kind: 'parts', title: 'definition', parts, sig };
    }
    // a name slot clicked directly: just the definiendum symbol
    if (c === 'name') return { kind: 'formula', tokens: [{ t: 'rel', s: symText(box) || '∅', impl: box.implicit }], sig };
    // a single formula / term / theorem
    if (isFolable(box)) { const r = toFOL(root, box, symText, sig); return { kind: 'formula', tokens: r.tokens, sig }; }
    // a composite slot clicked directly (conditions, inputs, proof, …): list its
    // renderable members — each shown on its own, NOT conjoined.
    const kids = kidsOf(box);
    const renderable = kids.filter((k) => { const cc = labelConcrete(k.label); return cc && (isFormulaish(k) || canonPath(cc).includes('term') || canonPath(cc).includes('formula') || isVariable(k)); });
    if (renderable.length) return { kind: 'list', title: c || 'items', items: renderable.map((k) => ({ tokens: toFOL(root, k, symText, sig).tokens, id: k.id })), sig };
    return { kind: 'none', reason: (c || 'this box') + ' — nothing to render' };
  }

  return {
    schema, ISA, HASA, ROOT_SLOTS, LABEL_SHORT, DERIVED_SYM, CONDITIONS, COUNTED_SLOT, ISA_PARENT,
    walk, find, parentOf, pieces, regionLen,
    isAbstract, isComposite, isLeafLabel, labelConcrete, canonPath,
    labelSubtypes, childCountsAs, pathsUnder, hasaSlotsOf, allowedLabelPaths,
    lblShort, derivedSymbol, labelTag,
    mergeIntervals, coverageOf, boxIssues, allIssues,
    scopeOf, isVariable, varsInScope, freshVarName, toFOL, folView, isFormulaish, isFolable, subtreeHasIssue,
  };
}
