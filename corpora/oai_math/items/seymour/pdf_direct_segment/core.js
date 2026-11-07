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

  return {
    schema, ISA, HASA, ROOT_SLOTS, LABEL_SHORT, DERIVED_SYM, CONDITIONS, COUNTED_SLOT, ISA_PARENT,
    walk, find, parentOf, pieces, regionLen,
    isAbstract, isComposite, isLeafLabel, labelConcrete, canonPath,
    labelSubtypes, childCountsAs, pathsUnder, hasaSlotsOf, allowedLabelPaths,
    lblShort, derivedSymbol, labelTag,
    mergeIntervals, coverageOf, boxIssues, allIssues,
    scopeOf, isVariable, varsInScope, freshVarName,
  };
}
