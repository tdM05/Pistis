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

// is a const name a "plumbing" constant we should treat as a numeric literal?
// OfNat.ofNat α n inst  → the literal n.
function ofNatLiteral(node) {
  if (node.kind === 'app' && node.fn && node.fn.kind === 'const' && node.fn.name === 'OfNat.ofNat') {
    const lit = (node.args || []).find((a) => a.kind === 'lit');
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
      const rawArgs = node.args || [];
      if (known) {
        const vals = rawArgs.slice(known.skip).map(normalize);
        if (known.shape === 'eq') return { t: 'eq', args: vals };
        if (known.shape === 'not') return { t: 'not', args: vals };
        if (known.shape === 'and') return { t: 'and', args: vals };
        if (known.shape === 'or') return { t: 'or', args: vals };
        if (known.shape === 'iff') return { t: 'iff', args: vals };
        if (known.shape === 'mem') return { t: 'mem', args: vals };   // [container, elem] or [elem, container]; aligner handles order
      }
      // generic application: head applied to its SIGNIFICANT args. We keep all
      // args here (can't know skip for unknown heads); the aligner trims by
      // matching arity against the NL side. Head may be a const (relation/fn
      // symbol) or a var (a matrix D applied to indices → function application).
      const headNode = normalize(head);
      return { t: 'app', head: headNode, args: rawArgs.map(normalize) };
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
  if (node.args) for (const a of node.args) if (occurs(name, a)) return true;
  return false;
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
