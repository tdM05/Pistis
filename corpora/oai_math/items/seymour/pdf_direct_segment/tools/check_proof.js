#!/usr/bin/env node
// check_proof.js — CLI view of the PROOF alignment. Thin wrapper over the ONE
// matcher: alignBox() in align_driver.js (the same path the UI's "align Lean"
// uses). alignBox dispatches a `proof` box (associated to Lean proof decls in
// lean_dict.json → proofs) to alignProof, which matches each NL step against the
// decls' propositions and locates Lean source spans. Here we just print the result.
//
//   node tools/check_proof.js [proofBoxId]   (default b10)   [--json]
import { readFileSync } from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import { makeCore } from '../core.js';
import { alignBox } from './align_driver.js';

const SEG = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const schema = JSON.parse(readFileSync(path.join(SEG, 'schema.json'), 'utf8'));
const ROOT = JSON.parse(readFileSync(path.join(SEG, 'tree.json'), 'utf8'));
const chars = readFileSync(path.join(SEG, 'chars.txt'), 'utf8');
const dict = JSON.parse(readFileSync(path.join(SEG, 'lean_dict.json'), 'utf8'));
const C = makeCore(schema);

const FLAGS = new Set(['--json', '--no-llm']);
const args = process.argv.slice(2).filter((a) => !FLAGS.has(a));
const JSONMODE = process.argv.includes('--json');
const LLM = !process.argv.includes('--no-llm');   // LLM routing of unfaithful steps (default on)
const boxId = args[0] || 'b10';
const box = C.find(ROOT, boxId);
if (!box) { console.error('no such box: ' + boxId); process.exit(1); }

const res = alignBox({ core: C, root: ROOT, box, chars, dict, llm: LLM });
if (!res.ok) { console.error('align failed: ' + res.reason); process.exit(1); }

const nlText = (id) => { const b = C.find(ROOT, id); const ps = b ? C.pieces(b) : []; return ps.length ? chars.slice(ps[0].start, ps[ps.length - 1].end).replace(/\s+/g, ' ').trim() : ''; };
// per-step verdict rows from the alignment children (each carries proofStep/verdict/witness).
const rows = (res.alignment.children || []).map((c) => {
  const id = c.proofStep || c.fol;
  const f = (res.findings || []).find((x) => x.fol === id);
  return { id, nl: nlText(id), verdict: c.verdict || (c.status === 'unmapped' ? 'unfaithful' : 'faithful'), witness: c.witness || null, finding: f || null };
});

if (JSONMODE) { console.log(JSON.stringify({ ok: true, leanDecl: res.leanDecl, rows, findings: res.findings, spans: res.spans })); process.exit(0); }

console.log(`proof ${boxId} ↔ Lean ${res.leanDecl}\n`);
for (const r of rows) {
  if (r.verdict === 'faithful') {
    console.log(`[${r.id}] ${r.nl.slice(0, 44).padEnd(45)} FAITHFUL  ↔ ${r.witness || ''}`);
  } else {
    console.log(`[${r.id}] ${r.nl.slice(0, 44).padEnd(45)} UNFAITHFUL`);
    if (r.finding) console.log(`        ${r.finding.message}   @ ${r.finding.leanLoc}`);
  }
}
