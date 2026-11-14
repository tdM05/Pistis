#!/usr/bin/env node
// edit.js — headless, SAFE mutation of tree.json. The write-side companion to
// inspect.js. Every command: mints ids / sorts children / merges pieces exactly
// like the UI, validates the label against the schema (core.js), writes tree.json
// in the SAME format the server uses (JSON.stringify indent 2, no trailing newline
// — byte-identical to serve.py's json.dump), and prints the touched box's issues.
//
//   node tools/edit.js set-label  <id> <a.b.c>        # relabel (dotted path); '-' clears
//   node tools/edit.js set-count  <id> <n|->          # set/clear count
//   node tools/edit.js set-var    <id> <vN|->         # set/clear variable name
//   node tools/edit.js set-sym    <id> <name|->       # set/clear authored symbol
//   node tools/edit.js set-pieces <id> <s-e,s-e,…|->  # set/clear text spans
//   node tools/edit.js add    <parentId> [--label a.b.c] [--pieces s-e,…] [--implicit] [--var vN] [--sym X] [--count n]
//   node tools/edit.js rm     <id>                    # delete a box + its subtree
//   node tools/edit.js move   <id> <newParentId|root> # reparent
//   node tools/edit.js wrap   <id,id,…> <a.b.c>       # wrap siblings in a new box
//   node tools/edit.js add-json <parentId> <@file|json>  # splice a whole subtree
//        (spec node: {label:"a.b.c", pieces:"s-e,s-e", var, sym, count, implicit, children:[…]})
//
// Label paths are the DOTTED full path as printed by inspect/allowed lists, e.g.
// `formula.atomic-formula.relation` or a slot like `inputs`. An invalid label is
// rejected with the list of what IS allowed under that parent (override: --force).
import { readFileSync, writeFileSync, existsSync } from 'fs';
import { fileURLToPath } from 'url';
import path from 'path';
import { makeCore } from '../core.js';

const dir = path.dirname(fileURLToPath(import.meta.url));
const R = path.resolve(dir, '..');
const schema = JSON.parse(readFileSync(path.join(R, 'schema.json'), 'utf8'));
const TREE = path.join(R, 'tree.json');
const ROOT = JSON.parse(readFileSync(TREE, 'utf8'));
const CHARS = existsSync(path.join(R, 'chars.txt')) ? readFileSync(path.join(R, 'chars.txt'), 'utf8') : '';
const C = makeCore(schema);

const die = (msg) => { console.error('✗ ' + msg); process.exit(1); };

// ── argv: command + positionals + --flags (flag with no following value = boolean) ──
const argv = process.argv.slice(2);
const cmd = argv[0];
const pos = []; const flags = {};
for (let i = 1; i < argv.length; i++) {
  const a = argv[i];
  if (a.startsWith('--')) { const k = a.slice(2); const nx = argv[i + 1];
    if (nx === undefined || nx.startsWith('--')) flags[k] = true; else { flags[k] = nx; i++; } }
  else pos.push(a);
}

// ── shared helpers (mirror ui/app.js) ──
let idCounter = 1;
C.walk(ROOT, (n) => { const m = /^b(\d+)$/.exec(n.id || ''); if (m) idCounter = Math.max(idCounter, +m[1] + 1); });
const mintId = () => 'b' + (idCounter++);
const regionStart = (b) => { const ps = C.pieces(b); return ps.length ? Math.min(...ps.map((p) => p.start)) : 0; };
const sortKids = (n) => { (n.children || []).sort((a, b) => regionStart(a) - regionStart(b)); };
const mergePieces = (b) => { if (!b.pieces) return; b.pieces.sort((x, y) => x.start - y.start);
  const out = []; for (const p of b.pieces) { const last = out[out.length - 1];
    if (last && p.start <= last.end) last.end = Math.max(last.end, p.end); else out.push({ ...p }); } b.pieces = out; };
const parsePieces = (s) => s === '-' ? [] : s.split(',').map((seg) => { const m = /^(\d+)-(\d+)$/.exec(seg.trim());
  if (!m) die(`bad piece "${seg}" — want start-end`); const start = +m[1], end = +m[2];
  if (end <= start) die(`bad piece ${seg} — end must exceed start`);
  if (CHARS && end > CHARS.length) die(`piece ${seg} past end of text (${CHARS.length})`); return { start, end }; });
const parseLabel = (s) => s === '-' ? null : s.split('.');
const must = (id) => { const b = C.find(ROOT, id); if (!b) die(`no such box: ${id}`); return b; };

// build a detached subtree from a spec {label?,pieces?,var?,sym?,count?,implicit?,
// children?}: mints ids, normalizes label (dotted→array) and pieces ("s-e,…"→objs),
// validates each node's label against ITS parent, recurses. Used by add-json.
const buildNode = (spec, parentNode) => {
  const node = { id: mintId(), pieces: [], children: [] };
  if (spec.label) node.label = typeof spec.label === 'string' ? spec.label.split('.') : spec.label;
  if (spec.pieces) node.pieces = typeof spec.pieces === 'string' ? parsePieces(spec.pieces)
    : spec.pieces.map((p) => Array.isArray(p) ? { start: p[0], end: p[1] } : p);
  mergePieces(node);
  if (spec.implicit) node.implicit = true;
  if (spec.var != null) node.var = spec.var;
  if (spec.sym != null) node.sym = spec.sym;
  if (spec.count != null) node.count = spec.count;
  checkLabel(parentNode, node.label);
  for (const ch of (spec.children || [])) node.children.push(buildNode(ch, node));
  sortKids(node);
  return node;
};

// validate a label-path against what the schema allows under `parent` (null = no
// check possible). Rejects unless --force. ROOT as parent uses ROOT_SLOTS.
const checkLabel = (parent, label) => {
  if (!label || flags.force) return;
  const allowed = C.allowedLabelPaths(ROOT, parent === ROOT ? null : parent);
  if (!allowed) return;   // parent has no declared slots → can't validate
  const key = label.join('.');
  if (!allowed.some((p) => p.join('.') === key))
    die(`label "${key}" not allowed under ${parent === ROOT ? 'paper' : parent.id}. allowed:\n  ` + allowed.map((p) => p.join('.')).join('\n  ') + '\n(override with --force)');
};

// write + report. `touched` = ids whose issues to show.
const commit = (action, touched) => {
  sortKids(C.parentOf(ROOT, touched[0]) || ROOT);
  writeFileSync(TREE, JSON.stringify(ROOT, null, 2));   // byte-identical to serve.py
  console.log('✓ ' + action);
  for (const id of touched) { const b = C.find(ROOT, id); if (!b) continue;
    const iss = C.boxIssues(b);
    console.log(`  ${id} [${b.label ? C.labelTag(ROOT, b) : 'unlabelled'}]: ${iss.length ? '⚠ ' + iss.join('; ') : 'ok'}`); }
  const all = C.allIssues(ROOT);
  console.log(`  tree: ${all.length ? all.length + ' box(es) with issues' : 'no structural issues'}`);
};

// ── commands ──
if (!cmd) die('usage: node tools/edit.js <command> …  (see header for commands)');

if (cmd === 'set-label') {
  const [id, lbl] = pos; if (!id || lbl === undefined) die('usage: set-label <id> <a.b.c|->');
  const b = must(id); const label = parseLabel(lbl); checkLabel(C.parentOf(ROOT, id) || ROOT, label);
  if (label) b.label = label; else delete b.label;
  commit(`set-label ${id} = ${label ? label.join('.') : '(cleared)'}`, [id]);
}
else if (cmd === 'set-count') {
  const [id, n] = pos; if (!id || n === undefined) die('usage: set-count <id> <n|->');
  const b = must(id); if (n === '-') delete b.count; else { const v = +n; if (!Number.isInteger(v) || v < 0) die('count must be a non-negative integer'); b.count = v; }
  commit(`set-count ${id} = ${n === '-' ? '(cleared)' : b.count}`, [id]);
}
else if (cmd === 'set-var') {
  const [id, v] = pos; if (!id || v === undefined) die('usage: set-var <id> <vN|->');
  const b = must(id); if (v === '-') delete b.var; else b.var = v;
  commit(`set-var ${id} = ${v === '-' ? '(cleared)' : b.var}`, [id]);
}
else if (cmd === 'set-sym') {
  const [id, s] = pos; if (!id || s === undefined) die('usage: set-sym <id> <name|->');
  const b = must(id); if (s === '-') delete b.sym; else b.sym = s;
  commit(`set-sym ${id} = ${s === '-' ? '(cleared)' : b.sym}`, [id]);
}
else if (cmd === 'set-pieces') {
  const [id, p] = pos; if (!id || p === undefined) die('usage: set-pieces <id> <s-e,…|->');
  const b = must(id); b.pieces = parsePieces(p); mergePieces(b);
  commit(`set-pieces ${id} = ${b.pieces.map((x) => x.start + '-' + x.end).join(',') || '(none)'}`, [id]);
}
else if (cmd === 'add') {
  const [parentId] = pos; if (!parentId) die('usage: add <parentId> [--label …] [--pieces …] [--implicit] [--var vN] [--sym X] [--count n]');
  const parent = parentId === 'root' ? ROOT : must(parentId);
  const label = flags.label ? parseLabel(flags.label) : null;
  checkLabel(parent, label);
  const box = { id: mintId(), pieces: flags.pieces ? parsePieces(flags.pieces) : [], children: [] };
  mergePieces(box);
  if (label) box.label = label;
  if (flags.implicit) box.implicit = true;
  if (flags.var) box.var = flags.var;
  if (flags.sym) box.sym = flags.sym;
  if (flags.count !== undefined && flags.count !== true) box.count = +flags.count;
  parent.children = parent.children || []; parent.children.push(box); sortKids(parent);
  writeFileSync(TREE, JSON.stringify(ROOT, null, 2));
  console.log(`✓ add ${box.id} under ${parentId}${label ? ' [' + label.join('.') + ']' : ''}`);
  const iss = C.boxIssues(box); console.log(`  ${box.id}: ${iss.length ? '⚠ ' + iss.join('; ') : 'ok'}`);
  const pIss = C.boxIssues(parent === ROOT ? { children: parent.children } : parent);
  if (parent !== ROOT) console.log(`  ${parent.id} [${parent.label ? C.labelTag(ROOT, parent) : 'unlabelled'}]: ${pIss.length ? '⚠ ' + pIss.join('; ') : 'ok'}`);
  console.log('  new id: ' + box.id);
}
else if (cmd === 'rm') {
  const [id] = pos; if (!id) die('usage: rm <id>');
  const b = must(id); const parent = C.parentOf(ROOT, id); if (!parent) die('cannot remove the root');
  const gone = new Set(); C.walk(b, (n) => gone.add(n.id));
  parent.children.splice(parent.children.indexOf(b), 1);
  if (ROOT.links) ROOT.links = ROOT.links.filter((l) => !gone.has(l.from) && !gone.has(l.to));
  writeFileSync(TREE, JSON.stringify(ROOT, null, 2));
  console.log(`✓ rm ${id} (${gone.size} box${gone.size > 1 ? 'es' : ''} removed)`);
  if (parent !== ROOT) console.log(`  ${parent.id} [${parent.label ? C.labelTag(ROOT, parent) : 'unlabelled'}]: ${(() => { const i = C.boxIssues(parent); return i.length ? '⚠ ' + i.join('; ') : 'ok'; })()}`);
  const all = C.allIssues(ROOT); console.log(`  tree: ${all.length ? all.length + ' box(es) with issues' : 'no structural issues'}`);
}
else if (cmd === 'move') {
  const [id, targetId] = pos; if (!id || !targetId) die('usage: move <id> <newParentId|root>');
  const box = must(id); const target = targetId === 'root' ? ROOT : must(targetId);
  if (target === box) die('cannot move a box onto itself');
  // not into own subtree
  let x = target; while (x) { if (x.id === id) die('cannot move a box into its own subtree'); x = C.parentOf(ROOT, x.id); }
  // span containment
  if (target !== ROOT) { const reg = C.mergeIntervals(C.pieces(target));
    const inside = C.pieces(box).every((p) => reg.some((r) => r.start <= p.start && p.end <= r.end));
    if (!inside && !flags.force) die(`"${box.id}" span lies outside "${target.id}" (override with --force)`); }
  // label allowed under target
  if (box.label && box.label.length && !flags.force) { const head = box.label[0];
    const slots = target === ROOT ? C.ROOT_SLOTS : C.hasaSlotsOf(target);
    if (!slots.some((s) => C.labelSubtypes(head, s))) die(`"${head}" not allowed inside "${target === ROOT ? 'paper' : C.labelConcrete(target.label) || target.id}" (override with --force)`); }
  const op = C.parentOf(ROOT, id); op.children.splice(op.children.indexOf(box), 1);
  target.children = target.children || []; target.children.push(box); sortKids(target);
  writeFileSync(TREE, JSON.stringify(ROOT, null, 2));
  console.log(`✓ move ${id} → ${targetId}`);
  const all = C.allIssues(ROOT); console.log(`  tree: ${all.length ? all.length + ' box(es) with issues' : 'no structural issues'}`);
}
else if (cmd === 'wrap') {
  const [idsArg, lbl] = pos; if (!idsArg || lbl === undefined) die('usage: wrap <id,id,…> <a.b.c>');
  const ids = idsArg.split(',').map((s) => s.trim()).filter(Boolean);
  const boxes = ids.map(must);
  const parent = C.parentOf(ROOT, ids[0]); if (!parent) die('cannot wrap top-level boxes under root this way');
  for (const id of ids) { if (C.parentOf(ROOT, id) !== parent) die(`all ids must share one parent — ${id} does not`); }
  const label = parseLabel(lbl); checkLabel(parent, label);
  const wrap = { id: mintId(), pieces: [], children: [] };
  if (label) wrap.label = label;
  // wrapper spans the union of the wrapped boxes' pieces
  wrap.pieces = C.mergeIntervals(boxes.flatMap((b) => C.pieces(b)));
  // remove the wrapped boxes from parent, attach under the wrapper (preserve order)
  parent.children = parent.children.filter((c) => !ids.includes(c.id));
  wrap.children = boxes; sortKids(wrap);
  parent.children.push(wrap); sortKids(parent);
  writeFileSync(TREE, JSON.stringify(ROOT, null, 2));
  console.log(`✓ wrap ${ids.join(',')} under ${wrap.id}${label ? ' [' + label.join('.') + ']' : ''}`);
  const iss = C.boxIssues(wrap); console.log(`  ${wrap.id}: ${iss.length ? '⚠ ' + iss.join('; ') : 'ok'}`);
  console.log('  new id: ' + wrap.id);
}
else if (cmd === 'add-json') {
  const [parentId, src] = pos; if (!parentId || src === undefined) die('usage: add-json <parentId> <@file.json|json-string>');
  const parent = parentId === 'root' ? ROOT : must(parentId);
  const raw = src.startsWith('@') ? readFileSync(src.slice(1), 'utf8') : src;
  let spec; try { spec = JSON.parse(raw); } catch (e) { die('bad json: ' + e.message); }
  const specs = Array.isArray(spec) ? spec : [spec];
  parent.children = parent.children || [];
  const added = [];
  for (const s of specs) { const n = buildNode(s, parent); parent.children.push(n); added.push(n.id); }
  sortKids(parent);
  writeFileSync(TREE, JSON.stringify(ROOT, null, 2));
  console.log(`✓ add-json: ${added.length} subtree(s) under ${parentId} → ${added.join(', ')}`);
  if (parent !== ROOT) { const i = C.boxIssues(parent); console.log(`  ${parent.id} [${parent.label ? C.labelTag(ROOT, parent) : 'unlabelled'}]: ${i.length ? '⚠ ' + i.join('; ') : 'ok'}`); }
  const all = C.allIssues(ROOT); console.log(`  tree: ${all.length ? all.length + ' box(es) with issues' : 'no structural issues'}`);
}
else if (cmd === 'fill-gaps') {
  // recursive "junk mop": for every non-leaf box in the subtree whose children
  // leave gaps in its span, add ONE commentary child covering exactly those gaps.
  const [id] = pos; if (!id) die('usage: fill-gaps <id>');
  const root = id === 'root' ? ROOT : must(id);
  const jobs = [];
  C.walk(root, (n) => { const c = n.label && C.labelConcrete(n.label);
    if (!n.children || !n.children.length) return;
    if (c && C.isLeafLabel(c)) return;          // leaf labels carry no sub-structure
    const cov = C.coverageOf(n); if (cov.gaps.length) jobs.push([n, cov.gaps]); });
  for (const [n, gaps] of jobs) {
    n.children.push({ id: mintId(), label: ['commentary'], pieces: gaps.map((g) => ({ start: g.start, end: g.end })), children: [] });
    sortKids(n);
  }
  writeFileSync(TREE, JSON.stringify(ROOT, null, 2));
  console.log(`✓ fill-gaps under ${id}: added ${jobs.length} commentary box(es)`);
  const all = C.allIssues(ROOT); console.log(`  tree: ${all.length ? all.length + ' box(es) with issues' : 'no structural issues'}`);
}
else die(`unknown command "${cmd}" — see header for commands`);
