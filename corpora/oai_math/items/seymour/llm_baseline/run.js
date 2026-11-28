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
import { makeCore } from './core.js';

const DIR = path.dirname(fileURLToPath(import.meta.url));
const argv = process.argv.slice(2);
const getFlag = (n, d) => { const i = argv.indexOf('--' + n); return i >= 0 && argv[i + 1] ? argv[i + 1] : d; };
const level = Number(getFlag('level', '1'));
const model = getFlag('model', 'us.anthropic.claude-opus-4-8');

const NL = fs.readFileSync(path.join(DIR, 'chars.txt'), 'utf8');

// The label tree is the project's EXACT schema (ISA + HASA), via core.js — the same
// logic the original UI uses. We never hardcode or reimplement it:
//   - allowedLabelPaths(root, box) → the full concrete label-PATHS valid as children
//     of `box` (ISA-expanded: e.g. formula → formula.compound-formula.quantified.universal).
//   - isLeafLabel(concrete) → a true terminal (atomic symbol / variable / constant):
//     can't be split further, exactly like commentary.
const SCHEMA = JSON.parse(fs.readFileSync(path.join(DIR, 'schema.json'), 'utf8'));
const C = makeCore(SCHEMA);
const ROOTBOX = { id: 'root', label: [], pieces: [{ start: 0, end: NL.length }], children: [] };
const concreteOf = (labelArr) => C.labelConcrete(labelArr);
const isComm = (c) => c === 'commentary';
const isOrg = (c) => c === 'organizer-section';
const needsMap = (c) => !isComm(c) && !isOrg(c);        // non-comm, non-org = formal → map
const needsVerdict = (c) => !isComm(c);                 // judge every non-comm box
// A box can be split further iff its concrete label is NOT a leaf label and not comm.
const canSplit = (c) => !isComm(c) && !C.isLeafLabel(c);

// Lean corpus (whole thing handed to each faithfulness judge — naive, no routing).
const leanDir = path.join(DIR, 'lean');
const leanFiles = fs.readdirSync(leanDir).filter((f) => f.endsWith('.lean')).sort();
const leanBlob = leanFiles.map((f) => `----- FILE: ${f} -----\n` + fs.readFileSync(path.join(leanDir, f), 'utf8')).join('\n\n');

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
let LAST_TX = null;    // repo-relative path of the most recent transcript file
let LAST_SID = null;   // claude session id of the most recent call (for --resume)
// Run claude headless with JSON output so we capture the session_id (lets us RESUME
// the same session/transcript for follow-ups, e.g. boundary disambiguation).
function runClaude(extraArgs, prompt, tag) {
  const seq = String(SEQ++).padStart(3, '0'); const t0 = Date.now();
  const raw = execFileSync('claude', ['-p', '--model', model, '--output-format', 'json', ...extraArgs],
    { input: prompt, encoding: 'utf8', maxBuffer: 64 * 1024 * 1024, timeout: 20 * 60 * 1000, stdio: ['pipe', 'pipe', 'inherit'] });
  let text = raw, sid = null;
  try { const j = JSON.parse(raw); if (j && typeof j === 'object') { if (j.result !== undefined) text = j.result; sid = j.session_id || null; } } catch (_) { /* not json — keep raw */ }
  const file = path.join(runDir(), `${seq}_${tag}.json`);
  try { fs.writeFileSync(file, JSON.stringify({ seq: +seq, tag, model, when: new Date().toISOString(), ms: Date.now() - t0, session_id: sid, prompt, reply: text }, null, 2)); } catch (e) { console.error('  [transcript] save failed:', e.message); }
  LAST_TX = path.relative(DIR, file); LAST_SID = sid;
  return text;
}
function callLLM(prompt, tag) { return runClaude([], prompt, tag); }
function resumeLLM(sid, prompt, tag) { return runClaude(['--resume', sid], prompt, tag); }
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
function parseObject(raw) {
  let s = (raw || '').trim(); const f = s.match(/```(?:json)?\s*([\s\S]*?)```/); if (f) s = f[1].trim();
  const a = s.indexOf('{'), b = s.lastIndexOf('}'); if (a < 0 || b <= a) return null;
  try { return JSON.parse(s.slice(a, b + 1)); } catch (_) { return null; }
}
function objectCall(prompt, tag) {
  let o = parseObject(callLLM(prompt, tag));
  if (o === null) o = parseObject(callLLM(prompt + '\n\nREMINDER: output ONLY a JSON object {"verdict":...,"reason":...}, nothing else.', tag + '_retry'));
  if (o === null) { FAILURES.push(tag); return { verdict: 'unknown', reason: `(judge gave no parseable verdict; see transcripts)` }; }
  return o;
}

// ---- faithfulness judge: one box's NL vs the whole Lean → {verdict,reason,map} -
// Formal boxes (needsMap) MUST map to a Lean declaration; an empty map means the
// claim is NOT formalized → unfaithful. org boxes are judged coarsely with no map.
function judgeText(nlText, label, mustMap, tag) {
  const tmpl = fs.readFileSync(path.join(DIR, 'prompts', 'judge.md'), 'utf8');
  const prompt = tmpl.replace('{{LABEL}}', label).replace('{{NL}}', nlText).replace('{{LEAN}}', leanBlob);
  console.error(`  [judge ${tag}] NL ~${Math.round(nlText.length / 4)}t vs ${leanFiles.length} lean files${mustMap ? ' (map required)' : ' (org, coarse)'}`);
  const o = objectCall(prompt, 'judge_' + tag);
  const v = String(o.verdict || '').toLowerCase();
  const map = Array.isArray(o.lean_map) ? o.lean_map.map(String) : (o.lean_map ? [String(o.lean_map)] : []);
  let verdict = v === 'faithful' ? 'ok' : v === 'unfaithful' ? 'notok' : 'unknown';
  if (mustMap && verdict === 'ok' && !map.length) verdict = 'notok';   // no map = not formalized
  return { verdict, reason: String(o.reason || ''), lean_map: map };
}
// Attach a verdict (+reason, +map) to a box in place.
function judgeBox(b, tag) {
  const { start, end } = b.pieces[0];
  const concrete = concreteOf(b.label);
  const mustMap = needsMap(concrete);
  const { verdict, reason, lean_map } = judgeText(NL.slice(start, end), concrete, mustMap, tag);
  b.verdict = verdict; b.reason = reason; b.transcript = LAST_TX;   // link box → its LLM transcript
  if (mustMap) b.lean_map = lean_map;
}

let idc = 1; const nid = () => 'b' + idc++;
function box(labelPath, lo, hi, children = []) { return { id: nid(), label: labelPath.slice(), pieces: [{ start: lo, end: hi }], children }; }

// ---- segment the region covered by `parentBox` into labelled, located parts ---
// The LLM is offered EXACTLY the concrete label-paths the schema allows as children
// of parentBox (ISA-expanded via core.allowedLabelPaths). It returns, per part, a
// full dotted label-path + the verbatim start text; we lock boundaries to the text.
function segmentRegion(parentBox, tag) {
  const lo = parentBox.pieces[0].start, hi = parentBox.pieces[0].end;
  const paths = C.allowedLabelPaths(ROOTBOX, parentBox === ROOTBOX ? ROOTBOX : parentBox);
  if (!paths || !paths.length) return null;               // nothing allowed below → terminal
  const allowedStr = [...new Set(paths.map((p) => p.join('.')))];
  const allowedSet = new Set(allowedStr);
  const fallback = allowedSet.has('organizer-section') ? ['organizer-section'] : allowedSet.has('commentary') ? ['commentary'] : allowedStr[0].split('.');
  const tmpl = fs.readFileSync(path.join(DIR, 'prompts', 'segment.md'), 'utf8');
  const prompt = tmpl.replace('{{NL}}', NL.slice(lo, hi)).replace('{{LABELS}}', allowedStr.join(', '));
  console.error(`  [segment ${tag}] [${lo},${hi}) · ${allowedStr.length} allowed label-paths`);
  const parts = arrayCall(prompt, 'segment_' + tag);
  const segSid = LAST_SID;   // the session that produced this segmentation (for resume)

  // Occurrences of `txt` in [lo,hi). The boundary is EXACT iff there is exactly one.
  const occurrencesOf = (txt) => { const o = []; if (!txt) return o; let k = NL.indexOf(txt, lo); while (k >= 0 && k + txt.length <= hi) { o.push(k); k = NL.indexOf(txt, k + 1); } return o; };

  const resolved = parts.map((p, i) => {
    const txt = (p.start_text || '').trim();
    const label = (p.label && allowedSet.has(String(p.label))) ? String(p.label).split('.') : fallback;
    if (i === 0) return { off: lo, label };
    const occ = occurrencesOf(txt);
    if (occ.length === 1) return { off: occ[0], label };        // unique → exact
    return { off: null, label, txt, occ };                      // 0 or >1 → resolve below
  });

  // DISAMBIGUATE the non-unique boundaries by RESUMING the same session: show the LLM
  // each candidate occurrence with just enough surrounding context to tell them apart,
  // and ask which one it meant. (Unique boundaries never hit the LLM again.)
  const amb = resolved.map((r, i) => (r.off === null && r.occ && r.occ.length > 1 ? { i, r } : null)).filter(Boolean);
  if (amb.length && segSid) {
    const letters = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
    const blocks = amb.map((a, k) => {
      const { txt, occ } = a.r;
      let c = 24; while (c < 600 && new Set(occ.map((o) => NL.slice(Math.max(0, o - c), o + txt.length + c))).size !== occ.length) c += 24;
      const ctx = Math.min(600, c * 2);
      const cands = occ.map((o, n) => `   ${n + 1}) …${NL.slice(Math.max(lo, o - ctx), o).replace(/\s+/g, ' ')}⟦▶START◀⟧${NL.slice(o, Math.min(hi, o + ctx)).replace(/\s+/g, ' ')}…`).join('\n');
      return `Marker ${letters[k]}  (start_text = ${JSON.stringify(txt)}) occurs ${occ.length} times — which one begins the part you intended?\n${cands}`;
    }).join('\n\n');
    const dp = `When you split the text just now, these start_text markers each occur MORE THAN ONCE, so I can't tell which occurrence you meant. For each marker, the ⟦▶START◀⟧ shows where that occurrence begins. Pick the occurrence that starts the part you intended.\n\n${blocks}\n\nOutput ONLY a JSON object mapping each marker letter to the chosen number, e.g. {"A": 2}.`;
    let pick = {}; try { pick = parseObject(resumeLLM(segSid, dp, 'segment_' + tag + '_disambig')) || {}; } catch (_) {}
    amb.forEach((a, k) => { const n = +pick[letters[k]]; const occ = a.r.occ; a.r.off = (n >= 1 && n <= occ.length) ? occ[n - 1] : occ[0]; });
  }
  // any still-unresolved (0 occurrences, or no session) → forward search from the
  // previous boundary, flagged. Keeps the tiling intact.
  let cursor = lo;
  resolved.forEach((r, i) => {
    if (r.off === null) {
      const occ = (r.occ && r.occ.length) ? r.occ : occurrencesOf(r.txt);
      const fwd = occ.find((o) => o >= cursor);
      r.off = fwd != null ? fwd : (occ[0] != null ? occ[0] : cursor);
      if (!occ.length) console.error(`    [${tag}] boundary ${i} start_text not found; kept cursor`);
    }
    r.off = Math.max(cursor, Math.min(r.off, hi)); cursor = r.off;
  });

  const segs = [];
  for (let i = 0; i < resolved.length; i++) {
    const s = resolved[i].off, e = i + 1 < resolved.length ? resolved[i + 1].off : hi;
    if (e > s) segs.push({ lo: s, hi: e, label: resolved[i].label });
  }
  if (!segs.length) segs.push({ lo, hi, label: fallback });
  segs[0].lo = lo; segs[segs.length - 1].hi = hi;
  return segs;
}

// ---- schema-driven recursive split → root box tree --------------------------
// Each box is split into schema-allowed children; a child recurses iff its concrete
// label canSplit (composite, not a leaf label, not comm) and depth remains. Each box
// stops on its own — siblings need not reach the same depth. depth below root = LEVEL.
function buildChildren(parentBox, depth, tag) {
  const segs = segmentRegion(parentBox, tag);
  if (!segs || segs.length <= 1) return null;             // can't split further here
  return segs.map((s, i) => {
    const b = box(s.label, s.lo, s.hi);
    if (depth > 1 && canSplit(concreteOf(s.label))) {
      const kids = buildChildren(b, depth - 1, `${tag}_${i}`);
      if (kids) b.children = kids;
    }
    return b;
  });
}
function runLevel(lvl) {
  if (lvl === 0) return [box(['organizer-section'], 0, NL.length)];
  return buildChildren(ROOTBOX, lvl, `L${lvl}`) || [box(['organizer-section'], 0, NL.length)];
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
  const children = runLevel(level);

  const gaps = checkTiling(children);
  if (gaps.length) { console.error(`[run] FATAL: top-level boxes do not tile — gaps ${JSON.stringify(gaps)}`); process.exit(1); }
  console.error(`[run] coverage OK: ${children.length} top boxes tile [0,${NL.length}) (0 gaps)`);

  // FAITHFULNESS PASS: LLM-judge only non-comm LEAVES. Formal leaves must map to the
  // Lean (empty map = not formalized = unfaithful); org leaves get a coarse verdict.
  // comm = terminal (no verdict). A box WITH children carries no verdict of its own —
  // the UI derives it by rolling up its children (any ✗ ⇒ ✗, all ✓ ⇒ ✓). No bias:
  // every judge call sees only its box's NL + the Lean, never any other verdict.
  const toJudge = [];
  const collect = (bs) => bs.forEach((b) => { const leaf = !(b.children && b.children.length); if (leaf && needsVerdict(concreteOf(b.label))) toJudge.push(b); if (!leaf) collect(b.children); });
  collect(children);
  console.error(`[run] judging ${toJudge.length} non-comm leaf box(es) for faithfulness...`);
  toJudge.forEach((b) => judgeBox(b, `${b.id}`));
  const vc = toJudge.reduce((m, b) => ((m[b.verdict] = (m[b.verdict] || 0) + 1), m), {});
  console.error(`[run] verdicts (leaves): ${JSON.stringify(vc)}`);

  const tree = { id: 'root', pieces: [], children, links: [], lean: {} };
  fs.writeFileSync(path.join(DIR, 'findings', `tree.level${level}.json`), JSON.stringify(tree, null, 2) + '\n');
  try {
    const rd = runDir();
    fs.writeFileSync(path.join(rd, 'tree.json'), JSON.stringify(tree, null, 2) + '\n');
    fs.writeFileSync(path.join(rd, 'manifest.json'), JSON.stringify({ level, model, when: new Date().toISOString(), runTs: RUN_TS, calls: SEQ, topBoxes: children.length, failures: FAILURES }, null, 2) + '\n');
  } catch (e) { console.error('  [snapshot] save failed:', e.message); }

  if (FAILURES.length) console.error(`[run] WARNING: failures ${FAILURES.join(', ')}`);
  console.error(`[run] wrote findings/tree.level${level}.json — ${children.length} top-level boxes:`);
  const dump = (bs, ind) => bs.forEach((c) => {
    const t = NL.slice(c.pieces[0].start, c.pieces[0].start + 42).replace(/\s+/g, ' ');
    const v = c.verdict ? ` ${c.verdict === 'ok' ? '✓' : c.verdict === 'notok' ? '✗' : '?'}` : '';
    console.error(`  ${ind}${c.id} ${concreteOf(c.label)}${v}  | ${t}`);
    if (c.children && c.children.length) dump(c.children, ind + '  ');
  });
  dump(children, '');
}
main();
