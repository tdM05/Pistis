// lean_spans — allocate a SOURCE SPAN (char range into the .lean file) for each
// aligned FOL box, so the Lean pane can highlight "this FOL piece ↔ this Lean
// text". Elaborated Expr nodes don't carry positions, so we render each node to
// its SURFACE form and locate that substring within the declaration BODY text,
// scoped to the parent's span so repeated tokens disambiguate.
//
// Reliable for written tokens/compounds (T, D, `D s j`, `(s, j) ∉ T`, `= 0`);
// purely synthesized nodes with no surface form fall back to the parent span.

// render a normalized Lean node (from lean_normalize) to its SURFACE string,
// approximating how it appears in source (so we can find it in the body text).
export function surface(n) {
  if (!n || typeof n !== 'object') return null;
  switch (n.t) {
    case 'var': return n.name;
    case 'const': return constSurface(n.name);
    case 'lit': return n.val;
    case 'app': {
      const as = (n.args || []).map(surface);
      // Prod.mk a b → "(a, b)"  (check BEFORE requiring a head surface — Prod.mk
      // has no surface token of its own; it's the tuple notation)
      if (n.head && n.head.t === 'const' && /Prod\.mk/.test(n.head.name)) {
        return as.every((x) => x != null) && as.length ? `(${as.join(', ')})` : null;
      }
      // matrix-as-function `D s j`, or a named fn applied: head + space-sep args
      const h = surface(n.head); if (h == null) return null;
      const okArgs = as.filter((x) => x != null);
      return [h, ...okArgs].join(' ');
    }
    case 'eq': { const a = surface(n.args[0]); const b = surface(n.args[1]); return (a != null && b != null) ? `${a} = ${b}` : null; }
    case 'not': {
      // ¬(x ∈ T) is written `x ∉ T` in source. If the sole arg is a mem, render
      // the ∉ form directly so it matches the body text.
      const inner = n.args && n.args[0];
      if (inner && inner.t === 'mem') return memSurface(inner, '∉');
      const a = surface(inner); return a != null ? `¬${a}` : null;
    }
    case 'mem': return memSurface(n, '∈');
    case 'arrow': { const a = surface(n.dom); const b = surface(n.body); return (a != null && b != null) ? `${a} → ${b}` : null; }
    case 'forall': { const b = surface(n.body); return b != null ? `∀ ${n.binder}, ${b}` : null; }
    default: return null;
  }
}
// render a `mem` node to source form `element ∈/∉ container`. Lean's explicit
// mem args elaborate as [container, element]; source writes element first.
function memSurface(n, op) {
  const args = n.args || [];
  if (args.length < 2) return null;
  const container = surface(args[0]); const element = surface(args[1]);
  return (container != null && element != null) ? `${element} ${op} ${container}` : null;
}
// a const's surface token. Plumbing/notation consts (Real, instances, dotted
// internal names) have no literal source token → null. A plain identifier (e.g. a
// decl name like `SupportedOn`, or `Fintype`) can be located by its own name.
function constSurface(name) {
  if (!name) return null;
  if (name === 'Real' || /\./.test(name) || /^Real\./.test(name)) return null;
  return /^[A-Za-z_][A-Za-z0-9_']*$/.test(name) ? name : null;
}

// pretty-print a normalized Lean node to a READABLE string for display (not for
// locating in source — this always returns something, unlike surface()). Shows the
// elaborated structure the aligner actually walks: ∀/→/¬/∈/=/application, so the
// user sees e.g. `∀ s j, ¬ (s, j) ∈ T → D s j = 0`.
export function pretty(n) {
  if (!n || typeof n !== 'object') return '?';
  switch (n.t) {
    case 'var': return n.name;
    case 'const': return n.name;
    case 'lit': return String(n.val);
    case 'sort': return 'Type';
    case 'forall': return `∀ ${n.binder}${n.dom ? ' : ' + pretty(n.dom) : ''}, ${pretty(n.body)}`;
    case 'lam': return `fun ${n.binder} => ${pretty(n.body)}`;
    case 'arrow': return `${pretty(n.dom)} → ${pretty(n.body)}`;
    case 'and': return (n.args || []).map(pretty).join(' ∧ ');
    case 'or': return (n.args || []).map(pretty).join(' ∨ ');
    case 'iff': return (n.args || []).map(pretty).join(' ↔ ');
    case 'not': { const a = n.args && n.args[0]; if (a && a.t === 'mem') return prettyMem(a, '∉'); return '¬ ' + pretty(a); }
    case 'mem': return prettyMem(n, '∈');
    case 'eq': return `${pretty(n.args[0])} = ${pretty(n.args[1])}`;
    case 'app': {
      if (n.head && n.head.t === 'const' && /Prod\.mk/.test(n.head.name)) return `(${(n.args || []).map(pretty).join(', ')})`;
      return [pretty(n.head), ...(n.args || []).map(pretty)].join(' ');
    }
    default: return n.t || '?';
  }
}
function prettyMem(n, op) { const a = n.args || []; if (a.length < 2) return 'mem(?)'; return `${pretty(a[1])} ${op} ${pretty(a[0])}`; }

// find the char range of `needle` within text[lo,hi), returned as absolute
// offsets {start,end} or null. Whitespace-tolerant (collapses runs of spaces).
export function locate(text, lo, hi, needle) {
  if (needle == null || needle === '') return null;
  const hay = text.slice(lo, hi);
  // exact first
  let i = hay.indexOf(needle);
  if (i >= 0) return { start: lo + i, end: lo + i + needle.length };
  // whitespace-insensitive: build a regex that allows flexible spacing
  const esc = needle.replace(/[.*+?^${}()|[\]\\]/g, '\\$&').replace(/\s+/g, '\\s+');
  const m = new RegExp(esc).exec(hay);
  if (m) return { start: lo + m.index, end: lo + m.index + m[0].length };
  return null;
}
