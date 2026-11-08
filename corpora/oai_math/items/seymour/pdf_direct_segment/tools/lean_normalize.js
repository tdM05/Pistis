// lean_normalize — turn the raw elaborated Expr JSON (from lean_extract) into a
// clean logical tree the aligner can walk, mirroring FOL structure.
//
// The kernel Expr is verbose: every application leads with universe/type/
// instance arguments (typeclass plumbing), connectives are `const` heads
// (`Not`, `Eq`, `Membership.mem`, `OfNat.ofNat`), and binders are nested
// `forall`/`lam`. This module collapses all that into nodes of shape:
//   {t:'forall'|'arrow'|'not'|'eq'|'rel'|'fn'|'app'|'const'|'var'|'sort'|'lit'|'lam',
//    name?, binder?, dom?, body?, args?[], head?}
// where `args` are only the SIGNIFICANT (explicit value) arguments.
//
// It does NOT decide FOL meaning — it only removes Lean plumbing so the aligner
// compares like-for-like. Interpreting `Not∘Membership.mem` as ∉, `Eq` as =,
// etc. is the aligner's job (next layer).

// Heads whose leading args are type/instance plumbing we drop, with how many
// leading args to skip and the logical shape to emit.
// skip = number of leading args that are universes/types/instances (not values).
const KNOWN = {
  'Eq':               { shape: 'eq',  skip: 1 },   // Eq (α) a b  → a = b
  'Not':              { shape: 'not', skip: 0 },   // Not p       → ¬p
  'And':              { shape: 'and', skip: 0 },
  'Or':               { shape: 'or',  skip: 0 },
  'Iff':              { shape: 'iff', skip: 0 },
  'Membership.mem':   { shape: 'mem', skip: 3 },   // mem (α)(γ)(inst) container elem (order varies by Lean ver)
};

// an app's args, each as {explicit, node}. Tolerates both the new wrapped shape
// ({explicit, node}) and a bare node (older cache / robustness).
function argNodes(appNode) {
  return (appNode.args || []).map((a) => (a && typeof a === 'object' && 'node' in a) ? a : { explicit: true, node: a });
}
// is a const name a "plumbing" constant we should treat as a numeric literal?
// OfNat.ofNat α n inst  → the literal n.
function ofNatLiteral(node) {
  if (node.kind === 'app' && node.fn && node.fn.kind === 'const' && node.fn.name === 'OfNat.ofNat') {
    const lit = argNodes(node).map((a) => a.node).find((a) => a && a.kind === 'lit');
    return lit ? { t: 'lit', val: lit.val } : { t: 'lit', val: '?' };
  }
  return null;
}

// collapse a raw Expr node into a logical node (recursive).
export function normalize(node) {
  if (!node || typeof node !== 'object') return { t: 'unknown' };
  switch (node.kind) {
    case 'var': return { t: 'var', name: node.name };
    case 'sort': return { t: 'sort' };
    case 'lit': return { t: 'lit', val: node.val };
    case 'const': return { t: 'const', name: node.name };
    case 'forall': {
      // genuine ∀ iff the bound var occurs in the body; else it's an arrow (→).
      const used = occurs(node.binder, node.body);
      if (used) return { t: 'forall', binder: node.binder, info: binfo(node.info), dom: normalize(node.dom), body: normalize(node.body) };
      return { t: 'arrow', dom: normalize(node.dom), body: normalize(node.body) };
    }
    case 'lam':
      return { t: 'lam', binder: node.binder, info: binfo(node.info), dom: normalize(node.dom), body: normalize(node.body) };
    case 'let':
      return { t: 'let', binder: node.binder, value: normalize(node.value), body: normalize(node.body) };
    case 'proj':
      return { t: 'proj', struct: node.struct, idx: node.idx, on: normalize(node.on) };
    case 'app': {
      const onf = ofNatLiteral(node); if (onf) return onf;
      const head = node.fn;
      const headName = head && head.kind === 'const' ? head.name : null;
      const known = headName && KNOWN[headName];
      // args now carry per-arg explicitness: {explicit, node}. Keep ONLY the
      // EXPLICIT (value) args — the implicit/instance leading args are plumbing.
      // This replaces the old "guess last N" trimming, so arity is exact.
      const explicitArgs = argNodes(node).filter((a) => a.explicit !== false).map((a) => a.node);
      if (known) {
        const vals = explicitArgs.map(normalize);
        if (known.shape === 'eq') return { t: 'eq', args: vals };
        if (known.shape === 'not') return { t: 'not', args: vals };
        if (known.shape === 'and') return { t: 'and', args: vals };
        if (known.shape === 'or') return { t: 'or', args: vals };
        if (known.shape === 'iff') return { t: 'iff', args: vals };
        if (known.shape === 'mem') return { t: 'mem', args: vals };
      }
      // generic application: head applied to its EXPLICIT args (exact, no guessing).
      // Head may be a const (relation/fn symbol) or a var (matrix D applied to
      // indices → function application).
      return { t: 'app', head: normalize(head), args: explicitArgs.map(normalize) };
    }
    default: return { t: 'unknown', kind: node.kind };
  }
}

function binfo(s) { return (s || '').replace('Lean.BinderInfo.', ''); }

// does bound-variable `name` occur anywhere in `node` (as a var)? Used to tell
// a genuine ∀ (binder used) from an arrow → (binder unused).
function occurs(name, node) {
  if (!node || typeof node !== 'object') return false;
  if (node.kind === 'var' && node.name === name) return true;
  for (const k of ['dom', 'body', 'fn', 'on', 'type', 'value']) if (node[k] && occurs(name, node[k])) return true;
  // raw app args are {explicit, node}; unwrap before recursing
  if (node.args) for (const a of node.args) { const inner = (a && typeof a === 'object' && 'node' in a) ? a.node : a; if (occurs(name, inner)) return true; }
  return false;
}

// collect every const name appearing in a normalized node (for verifying that a
// FOL sort predicate actually corresponds to a Lean binder TYPE — e.g. `real`
// discharges only if some binder's type really mentions `Real`/`ℝ`).
export function constNames(node, acc = new Set()) {
  if (!node || typeof node !== 'object') return acc;
  if (node.t === 'const' && node.name) acc.add(node.name);
  for (const k of ['dom', 'body', 'head', 'on', 'type', 'value']) if (node[k]) constNames(node[k], acc);
  if (node.args) for (const a of node.args) constNames(a, acc);
  return acc;
}

// peel the leading binder prefix of a normalized tree into {binders:[{binder,info,dom,kind}], body}.
// Collects both lam (definition value binders) and genuine forall (quantifiers).
export function peelBinders(n) {
  const binders = []; let cur = n;
  while (cur && (cur.t === 'lam' || cur.t === 'forall')) {
    binders.push({ binder: cur.binder, info: cur.info, dom: cur.dom, kind: cur.t });
    cur = cur.body;
  }
  return { binders, body: cur };
}

// peel the INPUT binders of a declaration's TYPE. A dependent function type
// `(x : A) → B` is a binder whether or not x is used in B — but normalize() turns
// an UNUSED one into `arrow` (dropping the binder name). So walk the RAW type
// here, collecting every leading forallE as an input binder with its domain.
// Returns [{binder, info, dom(normalized)}]. Stops at the result (non-forallE).
export function peelTypeBinders(rawType) {
  const out = []; let cur = rawType;
  while (cur && cur.kind === 'forall') {
    out.push({ binder: cur.binder, info: (cur.info || '').replace('Lean.BinderInfo.', ''), dom: normalize(cur.dom) });
    cur = cur.body;
  }
  return out;
}
