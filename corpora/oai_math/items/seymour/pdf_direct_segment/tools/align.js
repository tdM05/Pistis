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

// opts.binders: the Lean declaration's input binders, each {binder, typeConsts:
// Set<string>} — used to VERIFY a type-vs-prop discharge (a FOL sort predicate is
// only discharged if some binder's TYPE actually realizes it), rather than
// trusting the dictionary blindly.
export function makeAligner(core, dict = {}, symText = null, opts = {}) {
  const C = core;
  const binders = opts.binders || [];
  // ── leaf variable-identity tracking ──
  // Every FOL variable must map to a CONSISTENT Lean term everywhere it occurs
  // (coreferent FOL vars ⇒ coreferent Lean terms). We record each observation
  // `FOL-var → Lean-id` during the walk; afterwards, any FOL var seen mapping to
  // two different Lean ids is a faithfulness bug (e.g. v3 used as both D and T).
  // leanId: a canonical string for the Lean term a FOL var lands on.
  const varObs = {};   // folVar -> Set(canonical leanId)
  const obsNodes = {}; // folVar -> [report-node-ref] (to retro-flag on conflict)
  const tupleComps = {}; // folVar -> Set(component binder names) for declared tuples
  // discovered NL-symbol → Lean-symbol correspondence for THIS alignment. The
  // caller enforces it GLOBALLY (an NL relation/function must land on the SAME Lean
  // symbol across every step), which is what stops `∈` from matching `<`.
  const symObs = {};   // folSym -> Set(lean symbol name / node-type)
  const recordSym = (folSym, leanSym) => { if (!folSym || folSym === '∅' || !leanSym) return;
    (symObs[folSym] = symObs[folSym] || new Set()).add(leanSym); };
  const leanId = (n) => { if (!n) return '∅'; if (n.t === 'var') return 'v:' + n.name;
    if (n.t === 'const') return 'c:' + n.name; if (n.t === 'lit') return 'lit:' + n.val;
    if (n.t === 'app') return 'app:' + leanId(n.head) + '/' + (n.args ? n.args.length : 0); return n.t; };
  // record a FOL var's Lean identity. For a TUPLE var, landing on one of its
  // declared components (s / j) OR on the Prod.mk that packs them all counts as
  // the SAME canonical identity ('tuple:<var>') — so component-vs-pair is not a
  // false conflict; only landing OUTSIDE the tuple (e.g. on T) conflicts.
  const recordVar = (folVar, lean, reportNode) => { if (folVar == null) return;
    let id = leanId(lean);
    const comps = tupleComps[folVar];
    if (comps) {
      if (lean && lean.t === 'var' && comps.has(lean.name)) id = 'tuple:' + folVar;       // a component
      else if (lean && lean.t === 'app' && lean.head && lean.head.name && /Prod\.mk/.test(lean.head.name)) id = 'tuple:' + folVar; // the packed pair
    }
    (varObs[folVar] = varObs[folVar] || new Set()).add(id);
    (obsNodes[folVar] = obsNodes[folVar] || []).push({ node: reportNode, id }); };
  // a sort predicate `name` (dict entry {sort:true, lean:X}) is VERIFIED if some
  // Lean binder's type mentions the const X (e.g. real↦ℝ/Real, finite↦Fintype).
  // Returns the matched binder name, or null if no binder backs it up.
  const verifySort = (d) => {
    if (!d || !d.sort) return null;
    const want = (d.lean || '').replace('ℝ', 'Real');
    for (const b of binders) { if (b.typeConsts && (b.typeConsts.has(want) || [...b.typeConsts].some((c) => c.endsWith('.' + want) || c === want))) return b.binder; }
    return null;
  };
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

  // the fringe TERMS of a Lean node (vars / consts / lits / whole apps), left→right.
  // Used when an OPAQUE NL relation/function faces a Lean COMPOUND subtree (e.g. the
  // NL writes an atom `outside(x,T)` where Lean has `¬(x ∈ T)`): the NL atom absorbs
  // the subtree, and its argument terms line up against these fringe terms.
  const leafTerms = (n, acc = []) => { if (!n || typeof n !== 'object') return acc;
    if (n.t === 'var' || n.t === 'const' || n.t === 'lit' || n.t === 'app') { acc.push(n); return acc; }
    for (const k of ['dom', 'body']) if (n[k]) leafTerms(n[k], acc);
    if (Array.isArray(n.args)) n.args.forEach((a) => leafTerms(a, acc));
    return acc; };

  // strip Lean app plumbing: given a Lean app node and the number of operands the
  // FOL side expects, return the LAST n args (Lean leads with type/instance args).
  // Lean args are ALREADY trimmed to explicit-only by the normalizer, so the
  // significant args are simply all of them. (No more "guess last N" — a count
  // mismatch vs the FOL side is now surfaced by matchTerms as a finding.)
  const sigArgs = (leanArgs) => leanArgs;

  // the core recursive alignment of ONE fol node against ONE lean node.
  function alignNode(folBox, lean) {
    const fol = concreteNode(folBox);
    const shape = FOL_SHAPE[lc(fol)];
    const node = (status, note, children) => ({ fol: fol.id, lean: leanTag(lean), leanNode: lean, status, note: note || '', children: children || [] });

    if (!lean) return node('unmapped', 'no Lean counterpart');

    // INLINE local definitions so BODIES are compared (bounded — local let/define
    // values are small; NAMED notions like SupportedOn/rank stay folded as atoms):
    //   • Lean LOCAL let  E ↦ (D + Matrix.single s j 1)   [zeta]
    //   • NL `define`d     Dτ ↦ (D + τeₛeⱼᵀ)
    // Under strict structural faithfulness this correctly SURFACES genuine
    // differences — the leftover τ, `eₛeⱼᵀ` vs `single`, matrix vs linear map — as
    // reds (no false positives); it does not try to bridge them.
    while (lean && lean.t === 'var' && opts.letEnv && opts.letEnv[lean.name]) lean = opts.letEnv[lean.name];
    if (shape === 'var' && opts.nlDefs && fol.var != null && opts.nlDefs[fol.var]) return alignNode(opts.nlDefs[fol.var], lean);

    // ── definition-application: the NL applies a DEFINITION (e.g. "supported on"),
    // linked (name-evidence → the def box) to a def already associated with a Lean
    // decl in lean_dict.decls. It matches iff the Lean prop is HEADED by that decl.
    // Args aren't re-checked here (detector semantics: may over-claim), so a genuine
    // `SupportedOn T …` is never a false red; a non-`SupportedOn` prop mismatches.
    if (lc(fol) === 'definition-application') {
      const declLeaf = defAppDecl(fol);
      const lh = lean.t === 'app' ? (lean.head && lean.head.name) : (lean.t === 'const' ? lean.name : null);
      const ok = !!(declLeaf && lh && (lh === declLeaf || lh.endsWith('.' + declLeaf)));
      if (ok) recordSym('def:' + declLeaf, lh);
      return node(ok ? 'leaf' : 'mismatch', ok ? `defApp ↔ ${declLeaf}` : `defApp(${declLeaf || '?'}) vs Lean ${lh || lean.t}`);
    }

    // ── conjunction ──
    // Straight case: both sides are ∧ → pair positionally.
    // Type-vs-prop case: a FOL ∧ may meet a Lean node that ISN'T an ∧ because Lean
    // put some conjuncts in binder TYPES, not the proposition. We only set such a
    // conjunct aside if it is a sort predicate that is VERIFIED against an actual
    // Lean binder type (verifySort). Conjuncts that can't be verified are NOT
    // silently dropped — they are flagged. If, after removing verified-typed
    // conjuncts, more than one content conjunct remains, that's a real mismatch.
    if (shape === 'and') {
      const fkids = operandKids(fol);
      // the ONLY clean case: Lean is also an ∧, same number of conjuncts → pair.
      if (lean.t === 'and') {
        if ((lean.args || []).length !== fkids.length)
          return node('mismatch', `FOL conjunction has ${fkids.length} parts, Lean ∧ has ${(lean.args || []).length}`, pairChildren(fkids, lean.args || []));
        return node('match', '', pairChildren(fkids, lean.args || []));
      }
      // Lean is NOT an ∧ → the structures differ HERE. We STOP: the ∧ has no Lean
      // counterpart, so we do not descend into either conjunct (descending would
      // be aligning both sides against the same Lean node — the hack we removed).
      // We only annotate each conjunct with a one-line note for the report (no
      // recursion, no children aligned, nothing below gets mapped).
      // children are INFORMATIONAL only (the single finding is the ∧ mismatch
      // itself). A conjunct that's a verified typing predicate → 'typed'; the rest
      // are 'skipped' (NOT 'unmapped' — we did not check them, since we stopped at
      // the ∧, so we must not claim "no counterpart"). Neither is collected as a
      // separate finding.
      const children = fkids.map((k) => {
        const kn = concreteNode(k);
        const nm = lc(kn) === 'relation' ? relName(kn) : null;
        const binder = nm ? verifySort(dictOf(nm)) : null;
        const note = binder
          ? `${nm} corresponds to the TYPE of Lean binder '${binder}', not the body — your FOL puts in the body what Lean puts in a type`
          : 'not checked — alignment stopped at the ∧ above (this part may itself match Lean, but the ∧ has no Lean counterpart)';
        return { fol: kn.id, lean: null, status: binder ? 'typed' : 'skipped', note, children: [] };   // NO descent
      });
      return node('mismatch', `your text conjoins ${fkids.length} things here, but the Lean body is a single ${lean.t} (no ∧) — structures differ`, children);
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
      // the bound variable's name: the universal/existential box's variable-symbol
      // child (not the box itself).
      const vbox = (fol.children || []).find((k) => C.isVariable(k));
      const vName = (vbox && vbox.var) || fol.var || '?';
      const folBodyIsQuant = fbody && (FOL_SHAPE[lc(concreteNode(fbody))] === 'forall' || FOL_SHAPE[lc(concreteNode(fbody))] === 'exists');
      // ONE FOL variable may legitimately correspond to SEVERAL Lean binders when
      // it ranges over a tuple (v₅ ≡ (s,j): FOL `∀v₅` ↔ Lean `∀s ∀j`). But we only
      // absorb extra Lean binders if that tuple reading is VERIFIED: the FOL var
      // must actually be used as a tuple — i.e. it appears as the sole argument of
      // a relation/fn whose Lean realization is a Prod constructor (folVarIsTuple).
      let lbody = lean.body; const absorbed = [lean.binder];
      const wantN = folVarIsTuple(vName);   // declared tuple arity, or null
      if (!folBodyIsQuant && wantN) {
        while (lbody && lbody.t === want && absorbed.length < wantN) { absorbed.push(lbody.binder); lbody = lbody.body; }
        // register the component binder names so leaf occurrences of this tuple
        // var (as a component s/j, or as the packed Prod.mk) are seen as consistent
        tupleComps[vName] = new Set(absorbed);
      }
      let note;
      if (absorbed.length > 1) note = `∀${vName} ↔ ∀${absorbed.join(' ∀')} (one FOL var ≡ ${absorbed.length} Lean binders — declared ${wantN}-tuple)`;
      else if (!folBodyIsQuant && lean.body && lean.body.t === want) {
        return node('mismatch', `∀${vName} ↔ ∀${lean.binder}, but Lean binds another ∀${lean.body.binder} the FOL does not (declare ${vName} a tuple in lean_dict.json → tuples if intended)`, fbody ? [alignNode(fbody, lean.body)] : []);
      } else note = `∀${vName} ↔ ∀${lean.binder}`;
      return node('match', note, fbody ? [alignNode(fbody, lbody)] : []);
    }

    // ── relation / function application: ABSTRACT (no symbol dictionary) ──
    // Faithfulness does NOT check the symbol's IDENTITY. A non-logical relation or
    // function is OPAQUE: the only requirements are (1) Lean has SOME structure in
    // this position, and (2) the argument terms line up — variable consistency (run
    // after the walk) does the real checking. `=` is the one fixed relation (shape
    // 'eq', above); the logical connectives (∧∨¬→∀∃) are fixed too. Everything else
    // just maps to WHERE it lands in Lean; WHAT it is there is a discovered result,
    // never a precondition. So no `lean_dict.symbols` lookup here.
    if (shape === 'rel' || shape === 'app') {
      const fterms = termKids(fol);
      const name = shape === 'rel' ? relName(fol) : (fnSymName(fol) === '∅' ? '(implicit)' : fnSymName(fol));
      // membership is a LOGICAL primitive with a FIXED arg convention: Lean's `mem`
      // stores (container, element) but the NL writes (element, container). Pair by
      // that convention so `eₛ ∈ im Dτ` lines its element/container up with Lean's —
      // NOT blind-absorb (which mis-paired them and poisoned global consistency).
      if (lean.t === 'mem') {
        const ma = lean.args || [];
        const ordered = ma.length === 2 ? [ma[1], ma[0]] : ma;   // → (element, container)
        recordSym(name, 'mem');
        return node('leaf', `${name} ↔ ∈`, matchTerms(fterms, ordered));
      }
      if (lean.t !== 'app') {
        // a BARE Lean leaf (var/const/lit) has no sub-structure for the NL arguments
        // to land on — the NL applies to args Lean doesn't have here → structural
        // MISMATCH, not an absorb. (Stops NL `e(s)` being forced onto Lean's bare
        // vector `e`, which was mapping the index `s` onto `e` and poisoning others.)
        if (fterms.length && (lean.t === 'var' || lean.t === 'const' || lean.t === 'lit'))
          return node('mismatch', `${name} applies ${fterms.length} arg(s) but Lean has a bare ${lean.t}`);
        // genuine COMPOUND (not / and / …) → the opaque NL symbol ABSORBS that subtree.
        recordSym(name, lean.t);
        return node('leaf', `${name} ↔ ${lean.t}`, matchTerms(fterms, leafTerms(lean)));
      }
      const la = sigArgs(lean.args || [], fterms.length);     // explicit args only
      const lh = (lean.head && (lean.head.name || lean.head.t)) || 'app';
      // APPLY shape: ONLY a function whose symbol is IMPLICIT (juxtaposition — a
      // matrix/vector applied to indices, `D s j` / `xⱼ`) treats its FIRST term as
      // the function ↔ the Lean app HEAD, rest ↔ the Lean args (n == k+1). A NAMED
      // operation (explicit symbol: `mul`, `+`, or any relation) never does — its
      // args align positionally, and an ARITY difference is a real mismatch. This is
      // what keeps NL `τ·xⱼ` (one extra operand) from being silently absorbed into a
      // bare `xⱼ`: it stays a mismatch, surfacing the `τ`.
      if (shape === 'app' && fnSymImplicit(fol) && fterms.length === la.length + 1) {
        const kids = [alignNode(fterms[0], lean.head)];
        fterms.slice(1).forEach((t, i) => kids.push(alignNode(t, la[i])));
        return node('leaf', `${name} ↔ apply(${lh})`, kids);
      }
      if (fterms.length !== la.length)
        return node('mismatch', `${name} has ${fterms.length} argument(s), Lean ${lh} has ${la.length}`, matchTerms(fterms, la));
      recordSym(name, lh);
      return node('leaf', `${name} ↔ ${lh}`, matchTerms(fterms, la));
    }

    // ── leaves: variable / constant ──
    if (shape === 'var') {
      const vname = fol.var || '?';
      let r;
      if (lean.t === 'var') r = node('leaf', `${vname} ↔ ${lean.name}`);
      else if (lean.t === 'app') r = node('leaf', `${vname} ↔ ${lean.head && lean.head.name || 'app'}(…)`);
      else r = node('mismatch', `var ${vname} vs Lean ${lean.t}`);
      // record this FOL var's Lean identity for the post-walk consistency check
      recordVar(vname, lean, r);
      return r;
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
  // is the function-symbol IMPLICIT (no written glyph — pure juxtaposition)? Such a
  // node is a matrix/vector APPLICATION (`D s j`, `xⱼ`); a function-symbol with an
  // actual span (`mul`'s ·, `+`) is a NAMED operation. Drives apply-vs-named above.
  const fnSymImplicit = (b) => { const s = (b.children || []).find((k) => lc(k) === 'function-symbol'); return !s || s.implicit === true || !(s.pieces && s.pieces.length); };
  // the Lean decl leaf-name a definition-application applies: follow its
  // name-evidence's `def` link to the definition box, walk up to the box registered
  // in lean_dict.decls, and take that decl's last component (e.g. 'SupportedOn').
  const defAppDecl = (b) => {
    const nameEv = (b.children || []).find((k) => lc(k) === 'name-evidence') || b;
    const link = (opts.links || []).find((l) => l.from === nameEv.id && l.kind === 'def');
    if (!link || !opts.root || !opts.decls) return null;
    let x = C.find(opts.root, link.to);
    while (x) { if (opts.decls[x.id]) return opts.decls[x.id].decl.split('.').pop(); x = C.parentOf(opts.root, x.id); }
    return null;
  };
  const constName = (b) => symName(b);
  // symbol's authored name, else its slug (span text via symText), else ∅
  const symName = (b) => C.symNameOf(b, symText || (() => '∅'));

  // choose between two candidate Lean-arg orderings for a relation's terms: the
  // one under which more FOL vars match a Lean identity they ALREADY have recorded
  // (from other occurrences). No prior evidence → keep `asIs` (no silent guess);
  // the var-consistency pass will flag a genuinely wrong pairing either way.
  function betterPairing(fterms, asIs, swapped) {
    const score = (order) => { let s = 0; for (let i = 0; i < fterms.length; i++) {
      const fv = concreteNode(fterms[i]); const vn = fv && fv.var;
      if (vn && varObs[vn] && order[i]) { if (varObs[vn].has(leanId(order[i]))) s++; } }
      return s; };
    return score(swapped) > score(asIs) ? swapped : asIs;
  }
  // is FOL variable `vname` a tuple (so one ∀ over it ↔ several Lean binders)?
  // Verified, not guessed: it must be declared in dict.tuples (e.g. {"v5":2} says
  // v5 is a 2-tuple). No declaration → not a tuple → arity differences get flagged.
  function folVarIsTuple(vname) {
    const tuples = (opts.tuples || {});
    return (vname != null && tuples[vname] != null) ? tuples[vname] : null;   // the arity, or null
  }

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

  // top-level entry: align, then run the leaf variable-identity consistency pass.
  // A FOL var that mapped to >1 distinct Lean id is a faithfulness bug — retro-flag
  // every occurrence of it from 'leaf' to 'mismatch' with an explanatory note.
  function align(folBox, lean) {
    // reset observation state (aligner may be reused)
    for (const k in varObs) delete varObs[k];
    for (const k in obsNodes) delete obsNodes[k];
    for (const k in tupleComps) delete tupleComps[k];
    for (const k in symObs) delete symObs[k];
    const root = alignNode(folBox, lean);
    for (const v in varObs) {
      if (varObs[v].size > 1) {
        const ids = [...varObs[v]].join(', ');
        for (const { node: rn, id } of obsNodes[v]) {
          rn.status = 'mismatch';
          rn.note = `variable ${v} maps to INCONSISTENT Lean terms (${ids}) — here it is ${id}; a FOL variable must denote one thing everywhere`;
        }
      }
    }
    return root;
  }
  // observations discovered by the LAST align() call: each FOL variable's Lean
  // identities and each FOL symbol's Lean counterpart(s). The caller uses these to
  // enforce GLOBAL consistency across all steps of a proof.
  const observations = () => ({
    vars: Object.fromEntries(Object.entries(varObs).map(([k, v]) => [k, [...v]])),
    syms: Object.fromEntries(Object.entries(symObs).map(([k, v]) => [k, [...v]])),
  });
  return { align, alignNode, concreteNode, observations, _peel: null };
}
