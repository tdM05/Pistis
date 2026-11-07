#!/usr/bin/env node
// gen_docs.js — generate doc/labels.auto.md + doc/label_conditions.auto.md from
// schema.json, so the machine-readable rules always have a current human view.
// These are AUTO files; the hand-written doc/labels.md & label_conditions.md are
// authoritative prose and are never touched here.  Run: node tools/gen_docs.js
import { readFileSync, writeFileSync } from 'fs';
import { fileURLToPath } from 'url';
import path from 'path';

const dir = path.dirname(fileURLToPath(import.meta.url));
const R = path.resolve(dir, '..');
const s = JSON.parse(readFileSync(path.join(R, 'schema.json'), 'utf8'));

// ---- labels.auto.md: the is-a / has-a tree ----
const ISA = s.ISA, HASA = s.HASA;
const isAbstract = (l) => l in ISA, isComposite = (l) => l in HASA;
const kind = (l) => isAbstract(l) ? 'isa' : isComposite(l) ? 'hasa' : 'base';
let L = ['# Box Labels (auto-generated from schema.json — do not edit)\n',
  '`[isa]` = choose one subtype · `[hasa]` = decomposes into child boxes · `(base)` = leaf.',
  "`commentary` is auto-allowed under every composite box (omitted below).\n",
  `Top level (root) allows: ${s.ROOT_SLOTS.join(', ')}.\n`];
const seen = new Set();
const emit = (l, d, viaRef) => {
  const pad = '  '.repeat(d);
  const k = kind(l);
  if (viaRef && (seen.has(l) && (isAbstract(l) || isComposite(l)))) { L.push(`${pad}- →${l}`); return; }
  if (k === 'base') { L.push(`${pad}- ${l} (base)`); return; }
  seen.add(l);
  L.push(`${pad}- ${l} [${k}]`);
  const kids = k === 'isa' ? ISA[l] : HASA[l];
  kids.forEach((c) => emit(c, d + 1, true));
};
// show from the entry points (root slots) + any label never reached from them.
const entry = [...s.ROOT_SLOTS];
// also surface the symbol tree root (reached only as a has-a slot deep inside)
if ((ISA.symbol || HASA.symbol) && !entry.includes('symbol')) entry.push('symbol');
entry.forEach((r) => { seen.clear(); emit(r, 0, false); });
writeFileSync(path.join(R, 'doc/labels.auto.md'), L.join('\n') + '\n');

// ---- label_conditions.auto.md: arity + counted-slot tables ----
let K = ['# Label Structural Conditions (auto-generated from schema.json)\n',
  'Required child composition per label. A child counts as a slot if its concrete label IS-A the slot. commentary never counts.\n',
  '| label | required children |', '|---|---|'];
for (const [lab, conds] of Object.entries(s.CONDITIONS)) {
  K.push(`| ${lab} | ${conds.map((c) => `${c.min === c.max ? c.min : (c.max == null ? c.min + '+' : c.min + '–' + c.max)} ${c.slot}`).join(', ')} |`);
}
K.push('\n## Declared argument count (user must set box.count = number of)\n', '| label | counted slot |', '|---|---|');
for (const [lab, slot] of Object.entries(s.COUNTED_SLOT)) K.push(`| ${lab} | ${slot} |`);
K.push('\n## Auto-derived symbols (identity fixed by parent)\n', '| symbol label | parent → symbol |', '|---|---|');
for (const [sym, m] of Object.entries(s.DERIVED_SYM)) K.push(`| ${sym} | ${Object.entries(m).map(([p, g]) => `${p}→${g}`).join(', ')} |`);
writeFileSync(path.join(R, 'doc/label_conditions.auto.md'), K.join('\n') + '\n');

console.log('wrote doc/labels.auto.md and doc/label_conditions.auto.md');
