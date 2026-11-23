#!/usr/bin/env node
// run.js — NAIVE LLM baseline: reproduce what pdf_direct_segment does by HAND,
// but LLM-driven. The LLM segments the paper into LABELLED boxes (schema labels:
// organizer-section / commentary / definition / theorem) that TILE chars.txt,
// rendered by the UNMODIFIED original UI. Basics first: segmentation + labels +
// EXACT spans. (Faithfulness verdicts are a later layer.)
//
// EXACT SPANS: the LLM cannot count char offsets, and guessed offsets cut
// mid-formula. So the LLM returns each part's VERBATIM start text; we locate it in
// chars.txt by search (forward from the previous boundary) — every cut lands on a
// real token boundary, and we VERIFY the result tiles gap-free (like edit.js split
// / check_split.py). Only inputs: chars.txt + lean/*.lean.
//
// Levels (depth of segmentation, like the box tree's depth):
//   0: whole paper = one organizer-section box.
//   1: top-level tiling — the paper's sections (title/abstract/§1..§6/refs).
//   2: level 1, then each organizer-section split into its parts
//      (definition / theorem / commentary / nested organizer-section).
//
// Usage: node run.js --level {0|1|2} [--model us.anthropic.claude-opus-4-8]

import { execFileSync } from 'child_process';
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

const DIR = path.dirname(fileURLToPath(import.meta.url));
const argv = process.argv.slice(2);
const getFlag = (n, d) => { const i = argv.indexOf('--' + n); return i >= 0 && argv[i + 1] ? argv[i + 1] : d; };
const level = Number(getFlag('level', '1'));
const model = getFlag('model', 'us.anthropic.claude-opus-4-8');

const NL = fs.readFileSync(path.join(DIR, 'chars.txt'), 'utf8');
const ROOT_LABELS = ['organizer-section', 'commentary', 'definition', 'theorem'];
const SECTION_CHILD_LABELS = ['definition', 'theorem', 'commentary', 'organizer-section'];

// NL as anchored lines `@OFFSET|text` (offsets only help the LLM READ; the actual
// boundary is always re-derived from verbatim start_text, never from the anchor).
function anchoredNL(lo = 0, hi = NL.length) {
  const out = []; let off = 0;
  for (const line of NL.split('\n')) {
    const s = off, e = off + line.length;
    if (e >= lo && s < hi) out.push(`@${s}|${line}`);
    off = e + 1;
  }
  return out.join('\n');
}

// ---- transcripts (always-on, timestamped, never clobbered) ------------------
const RUN_TS = new Date().toISOString().replace(/[:.]/g, '-');
let RUN_DIR = null, SEQ = 0; const FAILURES = [];
function runDir() { if (!RUN_DIR) { RUN_DIR = path.join(DIR, 'findings', 'transcripts', `level${level}`, RUN_TS); fs.mkdirSync(RUN_DIR, { recursive: true }); } return RUN_DIR; }
function callLLM(prompt, tag) {
  const seq = String(SEQ++).padStart(3, '0'); const t0 = Date.now();
  const raw = execFileSync('claude', ['-p', '--model', model], { input: prompt, encoding: 'utf8', maxBuffer: 64 * 1024 * 1024, timeout: 20 * 60 * 1000, stdio: ['pipe', 'pipe', 'inherit'] });
  try { fs.writeFileSync(path.join(runDir(), `${seq}_${tag}.json`), JSON.stringify({ seq: +seq, tag, model, when: new Date().toISOString(), ms: Date.now() - t0, prompt, reply: raw }, null, 2)); } catch (e) { console.error('  [transcript] save failed:', e.message); }
  return raw;
}
function parseArray(raw) {
  let s = (raw || '').trim(); const f = s.match(/```(?:json)?\s*([\s\S]*?)```/); if (f) s = f[1].trim();
  const a = s.indexOf('['), b = s.lastIndexOf(']'); if (a < 0 || b <= a) return null;
  try { return JSON.parse(s.slice(a, b + 1)); } catch (_) { return null; }
}
function arrayCall(prompt, tag) {
  let arr = parseArray(callLLM(prompt, tag));
  if (arr === null) arr = parseArray(callLLM(prompt + '\n\nREMINDER: output ONLY a JSON array, nothing else.', tag + '_retry'));
  if (arr === null) { FAILURES.push(tag); throw new Error(`[${tag}] no JSON array after retry`); }
  return arr;
}

// ---- segment a region [lo,hi) into labelled, exactly-located parts ----------
function segmentRegion(lo, hi, allowed, tag) {
  const tmpl = fs.readFileSync(path.join(DIR, 'prompts', 'segment.md'), 'utf8');
  const prompt = tmpl.replace('{{NL}}', anchoredNL(lo, hi)).replace('{{LABELS}}', allowed.join(', '));
  console.error(`  [segment ${tag}] [${lo},${hi})`);
  const parts = arrayCall(prompt, 'segment_' + tag);
  // Locate each part's verbatim start_text; derive exact, token-aligned boundaries.
  const starts = []; let cursor = lo;
  parts.forEach((p, i) => {
    const txt = (p.start_text || '').trim();
    let off = i === 0 ? lo : NL.indexOf(txt, cursor);
    if (i > 0 && (off < 0 || off >= hi)) { const g = NL.indexOf(txt, lo); off = (g >= 0 && g < hi) ? g : cursor; console.error(`    [${tag}] boundary ${i} "${txt.slice(0, 24)}" not found forward; ${g >= 0 ? 'using earlier match' : 'keeping cursor'}`); }
    off = Math.max(cursor, Math.min(off, hi));
    starts.push({ off, label: allowed.includes(p.label) ? p.label : 'commentary' });
    cursor = off;
  });
  // build tiling segments [start_i, start_{i+1}) within [lo,hi)
  const segs = [];
  for (let i = 0; i < starts.length; i++) {
    const s = starts[i].off, e = i + 1 < starts.length ? starts[i + 1].off : hi;
    if (e > s) segs.push({ lo: s, hi: e, label: starts[i].label });
  }
  if (!segs.length) segs.push({ lo, hi, label: 'commentary' });
  segs[0].lo = lo; segs[segs.length - 1].hi = hi;      // clamp ends to the region
  return segs;
}

let idc = 1; const nid = () => 'b' + idc++;
function box(label, lo, hi, children = []) { return { id: nid(), label: [label], pieces: [{ start: lo, end: hi }], children }; }

// ---- level drivers → root box tree ------------------------------------------
function runLevel0() { return [box('organizer-section', 0, NL.length)]; }
function runLevel1() { return segmentRegion(0, NL.length, ROOT_LABELS, 'L1').map((s) => box(s.label, s.lo, s.hi)); }
function runLevel2() {
  const top = segmentRegion(0, NL.length, ROOT_LABELS, 'L2');
  return top.map((s, i) => {
    if (s.label !== 'organizer-section') return box(s.label, s.lo, s.hi);
    const kids = segmentRegion(s.lo, s.hi, SECTION_CHILD_LABELS, `L2_s${i}`).map((k) => box(k.label, k.lo, k.hi));
    return box('organizer-section', s.lo, s.hi, kids);
  });
}

// ---- coverage check: the top-level boxes must TILE [0,NL.length) ------------
function checkTiling(children) {
  const sorted = [...children].sort((a, b) => a.pieces[0].start - b.pieces[0].start);
  let cur = 0; const gaps = [];
  for (const c of sorted) { const { start, end } = c.pieces[0]; if (start !== cur) gaps.push([cur, start]); cur = Math.max(cur, end); }
  if (cur !== NL.length) gaps.push([cur, NL.length]);
  return gaps;
}

function main() {
  if (![0, 1, 2].includes(level)) { console.error('level must be 0, 1, or 2'); process.exit(1); }
  console.error(`[run] level ${level}, model ${model}`);
  const children = level === 0 ? runLevel0() : level === 1 ? runLevel1() : runLevel2();

  const gaps = checkTiling(children);
  if (gaps.length) { console.error(`[run] FATAL: top-level boxes do not tile — gaps ${JSON.stringify(gaps)}`); process.exit(1); }
  console.error(`[run] coverage OK: ${children.length} top boxes tile [0,${NL.length}) (0 gaps)`);

  const tree = { id: 'root', pieces: [], children, links: [], lean: {} };
  fs.writeFileSync(path.join(DIR, 'findings', `tree.level${level}.json`), JSON.stringify(tree, null, 2) + '\n');
  try {
    const rd = runDir();
    fs.writeFileSync(path.join(rd, 'tree.json'), JSON.stringify(tree, null, 2) + '\n');
    fs.writeFileSync(path.join(rd, 'manifest.json'), JSON.stringify({ level, model, when: new Date().toISOString(), runTs: RUN_TS, calls: SEQ, topBoxes: children.length, failures: FAILURES }, null, 2) + '\n');
  } catch (e) { console.error('  [snapshot] save failed:', e.message); }

  if (FAILURES.length) console.error(`[run] WARNING: failures ${FAILURES.join(', ')}`);
  console.error(`[run] wrote findings/tree.level${level}.json — ${children.length} top-level boxes:`);
  const short = { 'organizer-section': 'org', commentary: 'comm', definition: 'def', theorem: 'thm' };
  for (const c of children) {
    const t = NL.slice(c.pieces[0].start, c.pieces[0].start + 46).replace(/\s+/g, ' ');
    console.error(`  ${c.id} [${c.pieces[0].start},${c.pieces[0].end}) ${short[c.label[0]] || c.label[0]}${c.children.length ? ' +' + c.children.length : ''}  | ${t}`);
  }
}
main();
