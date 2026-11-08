// align — walk the NL-FOL box tree against the normalized Lean tree in lockstep,
// emitting an alignment: which FOL node corresponds to which Lean node, down to
// the leaves, plus MISMATCHES (structural disagreements = faithfulness findings).
//
// Deterministic rules (from the FOL↔Lean analysis):
//  - logical structure maps by shape: implication↔arrow, conjunction↔and,
//    disjunction↔or, negation↔not, equality↔eq, universal↔forall.
//  - a relation `outside(x,T)` whose dictionary entry is ∉ matches Lean
//    `not(mem(...))`; `membership`/`mem` handled via the dictionary.
//  - application: FOL function-application(head,args) ↔ Lean app(head,args) or a
//    matrix-as-function `var D` applied to indices.
//  - we HALT at leaves (relation-symbol / function-symbol / constant / variable)
//    and consult the symbol dictionary to confirm leaf identity.
//  - variables: FOL var ↔ Lean binder var, matched positionally through binders.
//  - a FOL conjunct that is a SORT predicate (marked in the dictionary) matches a
//    Lean BINDER TYPE rather than a body node (type-vs-prop); tracked separately.
//
// Output node: {fol:<id|null>, lean:<tag|null>, status:'match'|'mismatch'|'leaf'|'unmapped', note, children:[]}
// This module is pure. The caller supplies: the core (makeCore result), the FOL
// box to align, the normalized Lean tree (from lean_normalize), and a dictionary.

// FOL concrete-label → logical shape (what structural node it is)
const FOL_SHAPE = {
  implication: 'arrow', conjunction: 'and', disjunction: 'or', negation: 'not',
  equality: 'eq', universal: 'forall', existential: 'exists',
  relation: 'rel', 'function-application': 'app',
  variable: 'var', 'variable-symbol': 'var', constant: 'const',
};

export function makeAligner(core, dict = {}, symText = null) {
  const C = core;
  const lc = (b) => C.labelConcrete(b.label);
  // FOL children that are real content (skip commentary + the logical symbol boxes
  // like connective-symbol/quantifier/equality-symbol, which carry no operand).
  const SYMBOL_LABELS = new Set(['connective-symbol', 'quantifier', 'equality-symbol', 'relation-symbol', 'function-symbol', 'parenthesis']);
  const operandKids = (b) => (b.children || []).filter((k) => {
    const c = lc(k); return c && c !== 'commentary' && !SYMBOL_LABELS.has(c);
  });
  // descend through abstract wrapper boxes (formula/term/atomic-formula/body/…)
  // to the first concrete logical node.
  const concreteNode = (b) => {
    const c = lc(b);
    if (c && FOL_SHAPE[c]) return b;
    const kids = operandKids(b);
    if (kids.length === 1) return concreteNode(kids[0]);
    return b; // composite slot / unknown — return as-is
  };

  // dictionary lookup: FOL symbol name → {lean, sort?}  (sort=true means it's a
  // typing/sort predicate, matched against a binder type not a body node).
  const dictOf = (name) => dict[name] || null;

  // strip Lean app plumbing: given a Lean app node and the number of operands the
  // FOL side expects, return the LAST n args (Lean leads with type/instance args).
  const sigArgs = (leanArgs, n) => leanArgs.slice(Math.max(0, leanArgs.length - n));

  // the core recursive alignment of ONE fol node against ONE lean node.
  function alignNode(folBox, lean) {
    const fol = concreteNode(folBox);
    const shape = FOL_SHAPE[lc(fol)];
    const node = (status, note, children) => ({ fol: fol.id, lean: leanTag(lean), status, note: note || '', children: children || [] });

    if (!lean) return node('unmapped', 'no Lean counterpart');

    // ── conjunction: special-case the type-vs-prop split ──
    // A FOL `∧` whose conjuncts are partly SORT predicates (real, entries, …) may
    // meet a Lean node that ISN'T an `and`, because Lean put those facts in TYPES,
    // not the proposition. So: discharge sort-predicate conjuncts against binder
    // types, and align the remaining conjunct(s) against the Lean node itself.
    if (shape === 'and') {
      const fkids = operandKids(fol);
      if (lean.t === 'and') return node('match', '', pairChildren(fkids, lean.args || []));
      // Lean is NOT an ∧ → try to discharge sort conjuncts, leaving one content conjunct
      const sortKids = [], contentKids = [];
      for (const k of fkids) {
        const kn = concreteNode(k);
        const nm = lc(kn) === 'relation' ? relName(kn) : null;
        const d = nm ? dictOf(nm) : null;
        if (d && d.sort) sortKids.push({ box: kn, name: nm }); else contentKids.push(k);
      }
      if (contentKids.length === 1 && sortKids.length === fkids.length - 1) {
        const children = sortKids.map((s) => ({ fol: s.box.id, lean: null, status: 'typed', note: `${s.name} is a sort/typing predicate — carried by a Lean binder type, not the body`, children: [] }));
        children.push(alignNode(contentKids[0], lean));
        return node('match', 'type-vs-prop: sort conjunct(s) discharged to binder types', children);
      }
      return node('mismatch', `FOL conjunction vs Lean ${lean.t} (could not discharge sort conjuncts)`);
    }
    // ── other binary/unary logical connectives ──
    if (shape === 'arrow' || shape === 'or') {
      const want = shape === 'arrow' ? 'arrow' : shape;
      if (lean.t !== want) return node('mismatch', `FOL ${shape} vs Lean ${lean.t}`);
      const fkids = operandKids(fol);
      const lkids = shape === 'arrow' ? [lean.dom, lean.body] : (lean.args || []);
      return node('match', '', pairChildren(fkids, lkids));
    }
    if (shape === 'not') {
      if (lean.t !== 'not') return node('mismatch', `FOL negation vs Lean ${lean.t}`);
      const fk = operandKids(fol); const lk = lean.args || [];
      return node('match', '', pairChildren(fk, lk));
    }
    if (shape === 'eq') {
      if (lean.t !== 'eq') return node('mismatch', `FOL equality vs Lean ${lean.t}`);
      const fk = operandKids(fol); const lk = sigArgs(lean.args || [], fk.length);
      return node('match', '', pairChildren(fk, lk));
    }
    if (shape === 'forall' || shape === 'exists') {
      const want = shape === 'forall' ? 'forall' : 'exists';
      if (lean.t !== want) return node('mismatch', `FOL ${shape} vs Lean ${lean.t}`);
      const fbody = operandKids(fol).find((k) => isFormulaish(k)) || operandKids(fol)[0];
      // ONE FOL variable may correspond to SEVERAL Lean binders when it ranges
      // over a tuple (e.g. v₅ ≡ (s,j): FOL `∀v₅` ↔ Lean `∀s ∀j`). So absorb any
      // run of extra Lean binders of the same quantifier into this one FOL var,
      // as long as the FOL body is NOT itself another quantifier (which would
      // pair with the next Lean binder instead).
      let lbody = lean.body; const absorbed = [lean.binder];
      const folBodyIsQuant = fbody && (FOL_SHAPE[lc(concreteNode(fbody))] === 'forall' || FOL_SHAPE[lc(concreteNode(fbody))] === 'exists');
      if (!folBodyIsQuant) {
        while (lbody && lbody.t === want) { absorbed.push(lbody.binder); lbody = lbody.body; }
      }
      const note = `∀${fol.var || '?'} ↔ ∀${absorbed.join(' ∀')}` + (absorbed.length > 1 ? ` (one FOL var ≡ ${absorbed.length} Lean binders — tuple)` : '');
      return node('match', note, fbody ? [alignNode(fbody, lbody)] : []);
    }

    // ── relation: dictionary decides (e.g. outside ≡ ∉ → Lean not(mem)) ──
    if (shape === 'rel') {
      const symName = relName(fol);
      const d = dictOf(symName);
      // relation realized as negated membership: outside(x,T) ≡ ¬ (x ∈ T)
      if (d && d.lean === 'not-mem') {
        if (lean.t !== 'not' || !lean.args || lean.args[0].t !== 'mem')
          return node('mismatch', `${symName}≡∉ but Lean is ${lean.t}`);
        const mem = lean.args[0];
        // Lean `Membership.mem` elaborates as [container, element]; the math
        // reading is `element ∈ container`, matching FOL `outside(element, set)`.
        // So present mem args in (element, container) order for positional match.
        const memArgs = (mem.args || []).slice();
        const ordered = memArgs.length === 2 ? [memArgs[1], memArgs[0]] : memArgs;
        const fterms = termKids(fol);
        return node('leaf', `${symName} ≡ ∉`, matchTerms(fterms, ordered));
      }
      // plain relation ↔ Lean app with const head matching dict
      if (lean.t === 'app') {
        const lh = lean.head && lean.head.name;
        const fterms = termKids(fol);
        const la = sigArgs(lean.args || [], fterms.length);
        const ok = d && (d.lean === lh);
        return node(ok ? 'leaf' : 'mismatch', ok ? `${symName} ≡ ${lh}` : `${symName} ≡ ${d ? d.lean : '?'} vs Lean ${lh || lean.head.t}`, matchTerms(fterms, la));
      }
      return node('mismatch', `relation ${symName} vs Lean ${lean.t}`);
    }

    // ── function application: FOL fnapp(sym, terms) ↔ Lean app ──
    if (shape === 'app') {
      const fterms = termKids(fol);          // the argument terms
      const fsym = fnSymName(fol);           // the function symbol name (may be implicit)
      if (lean.t !== 'app') return node('mismatch', `function-application vs Lean ${lean.t}`);
      const fsymBox = (fol.children || []).find((k) => lc(k) === 'function-symbol');
      const fsymImplicit = fsymBox ? !!fsymBox.implicit : true;
      const d = fsym ? dictOf(fsym) : null;
      // APPLY semantics: a higher-order op where the FIRST FOL arg is the function
      // itself (e.g. val_at_entry(matrix, i, j) ≡ the Lean term `matrix i j`,
      // matrix applied to indices). Then: FOL arg0 ↔ Lean app HEAD, FOL args1.. ↔
      // Lean args. Triggered by dict {lean:'apply'} OR an IMPLICIT fn symbol with
      // a var-headed Lean app (the common "juxtaposition application" case).
      const applyByDefault = fsymImplicit && lean.head && lean.head.t === 'var';
      if ((d && d.lean === 'apply') || applyByDefault) {
        const head = fterms[0], rest = fterms.slice(1);
        const la = sigArgs(lean.args || [], rest.length);
        const children = [];
        children.push(alignNode(head, lean.head));           // matrix ↔ Lean head (D)
        rest.forEach((t, i) => children.push(alignNode(t, la[i])));
        return node('leaf', `apply: ${fsym === '∅' ? 'arg0' : fsym} is the function (matrix applied to indices)`, children);
      }
      const la = sigArgs(lean.args || [], fterms.length);
      const lh = lean.head && (lean.head.name || (lean.head.t === 'var' ? lean.head.name : lean.head.t));
      const note = d ? `${fsym} ≡ ${d.lean}` : (lh ? `fn↔${lh}` : 'fn↔?');
      return node('leaf', note, matchTerms(fterms, la));
    }

    // ── leaves: variable / constant ──
    if (shape === 'var') {
      const vname = fol.var || '?';
      if (lean.t === 'var') return node('leaf', `${vname} ↔ ${lean.name}`);
      // one FOL var ↔ a Lean compound (e.g. v₅ ↔ Prod.mk … s j)
      if (lean.t === 'app') return node('leaf', `${vname} ↔ ${lean.head && lean.head.name || 'app'}(…)`);
      return node('mismatch', `var ${vname} vs Lean ${lean.t}`);
    }
    if (shape === 'const') {
      const cname = constName(fol);
      const d = dictOf(cname);
      if (lean.t === 'lit') return node('leaf', `${cname} ≡ ${lean.val}`);
      if (lean.t === 'const') return node('leaf', `${cname} ≡ ${lean.name}`);
      return node('leaf', `${cname} ↔ ${lean.t}`);
    }

    return node('mismatch', `unhandled FOL shape ${shape || lc(fol)} vs Lean ${lean.t}`);
  }

  // pair up FOL operand children with Lean children positionally; length
  // mismatch is itself a finding (extra/missing operand).
  function pairChildren(fkids, lkids) {
    const out = []; const n = Math.max(fkids.length, lkids.length);
    for (let i = 0; i < n; i++) {
      if (i >= fkids.length) { out.push({ fol: null, lean: leanTag(lkids[i]), status: 'unmapped', note: 'Lean operand has no FOL counterpart', children: [] }); continue; }
      if (i >= lkids.length) { out.push({ fol: concreteNode(fkids[i]).id, lean: null, status: 'unmapped', note: 'FOL operand has no Lean counterpart', children: [] }); continue; }
      out.push(alignNode(fkids[i], lkids[i]));
    }
    return out;
  }
  // term lists (relation/fn arguments), matched positionally; a single FOL var vs
  // a Lean compound (Prod.mk) is allowed (1↔pair), handled in alignNode('var').
  function matchTerms(fterms, lterms) {
    const out = []; const n = Math.max(fterms.length, lterms.length);
    for (let i = 0; i < n; i++) {
      if (i >= fterms.length) { out.push({ fol: null, lean: leanTag(lterms[i]), status: 'unmapped', note: 'extra Lean arg', children: [] }); continue; }
      if (i >= lterms.length) { out.push({ fol: concreteNode(fterms[i]).id, lean: null, status: 'unmapped', note: 'extra FOL arg', children: [] }); continue; }
      out.push(alignNode(fterms[i], lterms[i]));
    }
    return out;
  }

  // ── FOL accessors ──
  const isFormulaish = (b) => C.isFormulaish(b);
  const termKids = (b) => operandKids(b).filter((k) => { const c = lc(k); return c !== 'relation-symbol'; });
  const relName = (b) => { const s = (b.children || []).find((k) => lc(k) === 'relation-symbol'); return s ? symName(s) : '∅'; };
  const fnSymName = (b) => { const s = (b.children || []).find((k) => lc(k) === 'function-symbol'); return s ? symName(s) : '∅'; };
  const constName = (b) => symName(b);
  // symbol's authored name, else its slug (span text via symText), else ∅
  const symName = (b) => C.symNameOf(b, symText || (() => '∅'));

  // short human tag for a Lean node (for the report)
  function leanTag(n) {
    if (!n) return null;
    switch (n.t) {
      case 'var': return 'var ' + n.name;
      case 'const': return n.name;
      case 'lit': return 'lit ' + n.val;
      case 'arrow': return '→';
      case 'and': return '∧'; case 'or': return '∨'; case 'not': return '¬';
      case 'eq': return '='; case 'mem': return '∈'; case 'forall': return '∀' + n.binder;
      case 'app': return 'app(' + (n.head && (n.head.name || n.head.t)) + ')';
      default: return n.t;
    }
  }

  return { alignNode, concreteNode, _peel: null };
}
