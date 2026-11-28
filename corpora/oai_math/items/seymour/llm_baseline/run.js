#!/usr/bin/env node
// run.js — NAIVE LLM baseline.
//
// WHAT:    the LLM segments the paper into schema-labelled boxes and judges each box's
//          faithfulness against the Lean, producing the box tree the UI renders.
// INPUTS:  chars.txt + lean/*.lean.
//
// COMMANDS:
//   run:     node run.js --level N
//   resume:  node run.js --continue <run-folder> --level N   (deepen an existing run)
//
// FLAGS (name — default — meaning):
//   --level N          1       tree depth to build (0 = whole paper as one box).
//   --model ID         us.anthropic.claude-opus-4-8   which model to call.
//   --mode M           headless   headless = no tools (pure naive baseline);
//                                  agentic  = grant read-only Read/Grep/Glob tools.
//   --lean-build       off     agentic only: also grant Bash (run lake/lean).
//   --retries K        2       clarify retries before a required span/boundary ABORTS.
//   --continue DIR     —       resume+deepen the run in DIR (else a new run folder).
//   --allow-mismatch   off     allow --continue under a different model/mode.

import { execFileSync } from 'child_process';
import fs from 'fs';
import os from 'os';
import path from 'path';
import { fileURLToPath } from 'url';
import { makeCore } from './core.js';

const DIR = path.dirname(fileURLToPath(import.meta.url));
const argv = process.argv.slice(2);
const getFlag = (n, d) => { const i = argv.indexOf('--' + n); return i >= 0 && argv[i + 1] ? argv[i + 1] : d; };
const level = Number(getFlag('level', '1'));
const model = getFlag('model', 'us.anthropic.claude-opus-4-8');
// How each LLM call is made:
//   headless (default) — one-shot `claude -p`, NO tools: the model answers purely from
//                        the inline prompt (the original naive baseline).
//   agentic            — the full Claude Code harness: grant read-only tools so the
//                        model can OPEN the item's files (lean/, chars.txt) to ground
//                        its answer and iterate. Same prompt, same levels — only the
//                        affordances differ, so headless-vs-agentic is comparable per
//                        level. --lean-build additionally grants Bash (e.g. to run
//                        lake/lean and actually check a claim); off by default.
const MODE = getFlag('mode', 'headless');
const LEAN_BUILD = argv.includes('--lean-build');
if (!['headless', 'agentic'].includes(MODE)) { console.error(`--mode must be 'headless' or 'agentic' (got '${MODE}')`); process.exit(1); }
if (LEAN_BUILD && MODE !== 'agentic') { console.error(`--lean-build requires --mode agentic`); process.exit(1); }
// Extra CLI args that turn a call into an agentic (tool-enabled) harness run. Empty in
// headless mode, so the headless invocation is byte-for-byte what it always was.
const AGENTIC_TOOLS = ['Read', 'Grep', 'Glob'].concat(LEAN_BUILD ? ['Bash'] : []);
function modeArgs() { return MODE === 'agentic' ? ['--allowedTools', AGENTIC_TOOLS.join(',')] : []; }
// Pipeline resume: --continue <run-folder> loads an existing run and DEEPENS it to the
// requested --level, reusing every split/verdict already computed (so levels nest and
// nothing is redone). A fresh run (no --continue) starts a new date+model+mode+id folder.
// NOTE: this is DISTINCT from the claude --resume used inside a call for disambiguation.
const CONTINUE_DIR = getFlag('continue', null);
const ALLOW_MISMATCH = argv.includes('--allow-mismatch');
if (!Number.isInteger(level) || level < 0) { console.error(`--level must be a non-negative integer (got '${getFlag('level', '1')}')`); process.exit(1); }
// How many clarify RETRIES a step gets before it ABORTS the whole run (so required
// spans/boundaries are never silently dropped — you inspect the transcript instead).
const RETRIES = (() => { const n = +getFlag('retries', '2'); return Number.isInteger(n) && n >= 0 ? n : 2; })();

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
const leanTexts = {};   // bare filename -> raw file text (span offsets are file-relative)
leanFiles.forEach((f) => { leanTexts[f] = fs.readFileSync(path.join(leanDir, f), 'utf8'); });
const leanBlob = leanFiles.map((f) => `----- FILE: ${f} -----\n` + leanTexts[f]).join('\n\n');

// ---- locate: the ONE substring-finder shared by NL boundaries and Lean spans ----
// The model gives a `target` (the exact substring it means) plus a larger `context`
// that contains the target, so we can pin it even when the target alone repeats.
// Returns {ok, start, end} (offsets into haystack) or {ok:false, why}.
function occurrencesIn(hay, sub, lo, hi) {
  const out = []; if (!sub) return out; let k = hay.indexOf(sub, lo);
  while (k >= 0 && k + sub.length <= hi) { out.push(k); k = hay.indexOf(sub, k + 1); } return out;
}
function locate(hay, target, context, lo = 0, hi = hay.length) {
  target = target || ''; context = context || '';
  if (!target) return { ok: false, why: 'empty target' };
  if (context && context.includes(target)) {
    const cocc = occurrencesIn(hay, context, lo, hi);
    if (cocc.length !== 1) return { ok: false, why: cocc.length ? `context occurs ${cocc.length}×` : 'context not found verbatim' };
    const cs = cocc[0], ce = cs + context.length;
    const tocc = occurrencesIn(hay, target, cs, ce);
    if (tocc.length !== 1) return { ok: false, why: tocc.length ? `target occurs ${tocc.length}× inside context` : 'target not inside context' };
    return { ok: true, start: tocc[0], end: tocc[0] + target.length };
  }
  // no usable context → the target alone must be unique
  const tocc = occurrencesIn(hay, target, lo, hi);
  if (tocc.length === 1) return { ok: true, start: tocc[0], end: tocc[0] + target.length };
  return { ok: false, why: tocc.length ? `target occurs ${tocc.length}× (needs context)` : 'target not found verbatim' };
}

// ---- run folder (date+model+mode+id) + transcripts --------------------------
// A RUN lives in findings/runs/<id>/ : tree.json (full internal tree = source of
// truth, carries pipeline flags), state.json (manifest + per-level stats), and
// transcripts/ (one file per LLM call). Per-level UI views are written as
// level<N>.json here AND mirrored to findings/tree.level<N>.json for the viewer.
const RUN_TS = new Date().toISOString().replace(/[:.]/g, '-');
const modelSlug = model.replace(/[^A-Za-z0-9]+/g, '-').replace(/^-+|-+$/g, '');
let RUN_DIR;           // absolute path to the run folder
if (CONTINUE_DIR) {
  RUN_DIR = path.isAbsolute(CONTINUE_DIR) ? CONTINUE_DIR : path.resolve(process.cwd(), CONTINUE_DIR);
  if (!fs.existsSync(path.join(RUN_DIR, 'tree.json'))) { console.error(`--continue: no tree.json found in ${RUN_DIR}`); process.exit(1); }
} else {
  RUN_DIR = path.join(DIR, 'findings', 'runs', `${RUN_TS}_${modelSlug}_${MODE}${LEAN_BUILD ? '-lb' : ''}_${Math.random().toString(36).slice(2, 6)}`);
  fs.mkdirSync(RUN_DIR, { recursive: true });
}
const TRANSCRIPT_DIR = path.join(RUN_DIR, 'transcripts');
let SEQ = 0; const FAILURES = [];
function runDir() { if (!fs.existsSync(TRANSCRIPT_DIR)) fs.mkdirSync(TRANSCRIPT_DIR, { recursive: true }); return TRANSCRIPT_DIR; }
// on resume, continue transcript numbering past what's already there (never clobber)
if (CONTINUE_DIR && fs.existsSync(TRANSCRIPT_DIR)) {
  const nums = fs.readdirSync(TRANSCRIPT_DIR).map((f) => parseInt(f, 10)).filter((n) => !Number.isNaN(n));
  SEQ = nums.length ? Math.max(...nums) + 1 : 0;
}
let LAST_TX = null;    // repo-relative path of the most recent transcript file
let LAST_SID = null;   // claude session id of the most recent call (for --resume)
// atomic JSON write (tmp + rename) so a crash mid-write can never corrupt a file.
function writeJSONAtomic(file, obj) { const tmp = file + '.tmp'; fs.writeFileSync(tmp, JSON.stringify(obj, null, 2) + '\n'); fs.renameSync(tmp, file); }
// HARD STOP a step that could not get a required span/boundary after RETRIES retries.
// Prior boxes are already persisted (per-box), so --continue resumes from here; the
// full call-by-call log (initial + every retry) is in the run's transcripts/ for you to
// inspect exactly what the model kept producing.
function abort(tag, msg) {
  console.error(`\n[run] ABORT at ${tag}: ${msg}`);
  console.error(`[run] retries exhausted (--retries ${RETRIES}). Inspect the full log: ${path.relative(DIR, TRANSCRIPT_DIR)}/`);
  console.error(`[run] resume after fixing with: node run.js --continue ${path.relative(DIR, RUN_DIR)} --level ${level}`);
  process.exit(2);
}
// Run claude with JSON output so we capture the session_id (lets us RESUME the same
// session/transcript for follow-ups, e.g. boundary disambiguation). In agentic mode
// `modeArgs()` adds --allowedTools so the SAME call becomes a tool-enabled harness
// run; headless mode adds nothing, so the invocation is unchanged. The claude process
// runs with cwd=DIR so any file tools resolve against the item directory (lean/,
// chars.txt); this is inert for a no-tool headless call.
// ---- agentic sandbox (proot) ------------------------------------------------
// Agentic mode grants the model real tools, so it must NOT be able to reach the repo /
// human ground truth (../pdf_direct_segment/tree.json). OS namespaces (bwrap) are off
// here, so we use proot — an unprivileged, ptrace-based filesystem jail that remaps the
// root for claude AND every process it spawns (shell, lean, lake). The jail exposes ONLY
// resolved copies of the lean files + chars.txt (as /work) plus the minimum needed to run
// claude; the repo is never mounted, so no tool/shell can read it by any path.
const PROOT = (() => {
  for (const c of [getFlag('proot', null), process.env.PROOT, path.join(DIR, 'tools', 'proot')]) {
    if (!c) continue; try { fs.accessSync(c, fs.constants.X_OK); return c; } catch (_) {}
  }
  return null;
})();
let SANDBOX = null;   // built lazily on the first agentic call
function ensureSandbox() {
  if (SANDBOX) return SANDBOX;
  if (!PROOT) { console.error(`[run] FATAL: agentic mode needs proot (unprivileged sandbox) but none found. Put the static binary at ${path.relative(DIR, path.join(DIR, 'tools', 'proot'))} or pass --proot <path> / PROOT=<path>.`); process.exit(3); }
  const base = fs.mkdtempSync(path.join(os.tmpdir(), 'pistis-sbx-'));   // OUTSIDE the repo
  const jail = path.join(base, 'root'), jtmp = path.join(base, 'tmp'), work = path.join(base, 'work');
  const shm = path.join(base, 'shm'), cfg = path.join(base, 'claude-cfg');
  fs.mkdirSync(jail); fs.mkdirSync(jtmp); fs.mkdirSync(shm); fs.mkdirSync(cfg); fs.mkdirSync(path.join(work, 'lean'), { recursive: true });
  leanFiles.forEach((f) => fs.writeFileSync(path.join(work, 'lean', f), leanTexts[f]));   // resolved copies, no symlink
  fs.writeFileSync(path.join(work, 'chars.txt'), NL);
  const HOME = os.homedir(); let alt = null; try { const r = fs.realpathSync(HOME); if (r !== HOME) alt = r; } catch (_) {}
  // FRESH, MEMORY-WIPED ~/.claude: copy ONLY auth (+ settings) into a writable throwaway
  // dir. We must NOT bind the real ~/.claude — it holds history.jsonl / projects / sessions
  // / shell-snapshots, i.e. prior conversations that could reveal the ground truth. The
  // jailed agent gets a blank-slate config: it can authenticate but has no memory.
  for (const f of ['.credentials.json', 'settings.json']) { const src = path.join(HOME, '.claude', f); if (fs.existsSync(src)) { fs.copyFileSync(src, path.join(cfg, f)); try { fs.chmodSync(path.join(cfg, f), 0o600); } catch (_) {} } }
  const binds = [];
  for (const [src, dst] of [['/usr', '/usr'], ['/usr/bin', '/bin'], ['/lib', '/lib'], ['/lib64', '/lib64'], ['/etc', '/etc'], ['/dev', '/dev'], ['/proc', '/proc']]) if (fs.existsSync(src)) binds.push('-b', `${src}:${dst}`);
  binds.push('-b', `${shm}:/dev/shm`);   // private empty shared-memory (overrides /dev/shm; no cross-process leak)
  binds.push('-b', `${jtmp}:/tmp`);
  // ONLY the home subtrees claude (and, for --lean-build, lean) needs — both HOME mount
  // aliases (e.g. /u/taddmao and /h/56/taddmao). The real ~/.claude is NOT here; the fresh
  // `cfg` is bound in its place. Nothing else of HOME is exposed.
  const subs = ['.local/bin', '.local/share/claude', '.config', '.nvm'].concat(LEAN_BUILD ? ['.elan', '.cache'] : []);
  for (const h of [HOME, alt].filter(Boolean)) {
    for (const s of subs) { const p = path.join(h, s); if (fs.existsSync(p)) binds.push('-b', `${p}:${p}`); }
    binds.push('-b', `${cfg}:${path.join(h, '.claude')}`);   // blank-slate ~/.claude (auth only)
  }
  binds.push('-b', `${work}:/work`);
  const argvPrefix = ['-r', jail, ...binds, '-w', '/work'];
  const env = { ...process.env, HOME, PATH: `${path.join(HOME, '.local/bin')}:/usr/bin:/bin` };
  SANDBOX = { base, argvPrefix, env };
  console.error(`  [sandbox] proot jail ${path.relative(process.cwd(), base) || base} — lean/+chars.txt only; repo hidden; fresh (memory-wiped) ~/.claude; private /dev/shm`);
  return SANDBOX;
}

function runClaude(extraArgs, prompt, tag) {
  const seq = String(SEQ++).padStart(3, '0'); const t0 = Date.now();
  const claudeArgs = ['-p', '--model', model, '--output-format', 'json', ...modeArgs(), ...extraArgs];
  // headless = bare claude (no tools, nothing to jail). agentic = claude inside the proot jail.
  let execFile, execArgs, execEnv;
  if (MODE === 'agentic') { const sb = ensureSandbox(); execFile = PROOT; execArgs = [...sb.argvPrefix, 'claude', ...claudeArgs]; execEnv = sb.env; }
  else { execFile = 'claude'; execArgs = claudeArgs; execEnv = process.env; }
  const raw = execFileSync(execFile, execArgs,
    { input: prompt, encoding: 'utf8', cwd: DIR, env: execEnv, maxBuffer: 64 * 1024 * 1024, timeout: 30 * 60 * 1000, stdio: ['pipe', 'pipe', 'inherit'] });
  let text = raw, sid = null, meta = {};
  try {
    const j = JSON.parse(raw);
    if (j && typeof j === 'object') {
      if (j.result !== undefined) text = j.result;
      sid = j.session_id || null;
      // agentic runs report how much the harness did — record it so we can SEE that
      // tools engaged (num_turns > 1) and what it cost, without stream parsing.
      for (const k of ['num_turns', 'total_cost_usd', 'duration_ms', 'duration_api_ms', 'is_error']) if (j[k] !== undefined) meta[k] = j[k];
    }
  } catch (_) { /* not json — keep raw */ }
  const file = path.join(runDir(), `${seq}_${tag}.json`);
  try { fs.writeFileSync(file, JSON.stringify({ seq: +seq, tag, mode: MODE, leanBuild: LEAN_BUILD, model, when: new Date().toISOString(), ms: Date.now() - t0, session_id: sid, ...meta, prompt, reply: text }, null, 2)); } catch (e) { console.error('  [transcript] save failed:', e.message); }
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

// locate one requested span {file,target,context,approx?} within its file's text →
// {ok, span:{file,start,end,approx?}} (file-relative offsets, 'lean/<name>' form) or
// {ok:false,why}. `approx` (an anchor "where it should be", not a real counterpart) is
// carried through from the request.
function locateLeanSpan(e) {
  const file = String(e && e.file || '').replace(/^lean\//, '').trim();
  const txt = leanTexts[file];
  if (!txt) return { ok: false, why: `unknown file '${e && e.file}'` };
  const r = locate(txt, String(e.target || '').trim(), String(e.context || '').trim());
  if (!r.ok) return { ok: false, why: r.why };
  const span = { file: 'lean/' + file, start: r.start, end: r.end };
  if (e.approx) span.approx = true;
  return { ok: true, span };
}
const parseSpanList = (o) => (o && Array.isArray(o.lean_spans) ? o.lean_spans : (o && o.lean_spans ? [o.lean_spans] : []));

// ---- faithfulness judge: one box's NL vs the whole Lean ----------------------
// TWO span channels, both located via {file,target,context} (target disambiguated by
// context, `approx:true` = an anchor where something SHOULD be rather than a real
// counterpart):
//   • box mapping (`lean_spans`): where the box corresponds in Lean. Formal boxes MUST
//     have >=1; if nothing corresponds, a single approx anchor. A box counts as really
//     formalized only via a NON-approx span.
//   • per-reason spans (`reason[i]` = {text,file,target,context,approx?}): EVERY distinct
//     unfaithfulness item carries its own span (exact offending fragment, or an approx
//     anchor marking where the missing thing belongs). [] when faithful.
// Required spans (mustMap boxes only) are RETRIED up to RETRIES; if any still can't be
// obtained, the run ABORTS (never a silent drop). org/commentary need no span.
function judgeText(nlText, label, mustMap, tag) {
  const tmpl = fs.readFileSync(path.join(DIR, 'prompts', 'judge.md'), 'utf8');
  const prompt = tmpl.replace('{{LABEL}}', label).replace('{{NL}}', nlText).replace('{{LEAN}}', leanBlob);
  console.error(`  [judge ${tag}] NL ~${Math.round(nlText.length / 4)}t vs ${leanFiles.length} lean files${mustMap ? ' (span map required)' : ' (org — no span required)'}`);
  const o = objectCall(prompt, 'judge_' + tag);
  const v = String(o.verdict || '').toLowerCase();

  // collect every REQUIRED span request so they share the retry/abort policy. Each pending
  // item has a `desc` (shown to the model on retry) and a `sink` that receives the located
  // span. Required spans (only for mustMap boxes — org/comm need none) come from:
  //   (a) a span the model gave that we could not locate,
  //   (b) NO box-mapping span at all → demand one (exact, or an approx anchor),
  //   (c) a reason with no locatable span → demand one (every error carries a span).
  const pending = [];
  const mapSpans = [];
  parseSpanList(o).forEach((e) => {
    const r = locateLeanSpan(e);
    if (r.ok) mapSpans.push(r.span);
    else if (mustMap) pending.push({ desc: `the box-mapping span (your file=${JSON.stringify(e && e.file)} target=${JSON.stringify(e && e.target)} could not be located: ${r.why})`, sink: (s) => mapSpans.push(s) });
  });
  if (mustMap && !mapSpans.length && !pending.length) pending.push({ desc: `the box-mapping span for this ${label}: where it is formalized in the Lean, or exactly ONE approx anchor (approx:true) marking where it should be`, sink: (s) => mapSpans.push(s) });

  // reason entries: {text,file,target,context,approx} (bare string accepted as legacy).
  const reasonReq = Array.isArray(o.reason) ? o.reason : (o.reason != null ? [o.reason] : []);
  const reasons = [];
  reasonReq.forEach((e) => {
    const text = typeof e === 'string' ? e.trim() : String((e && e.text) || '').trim();
    if (!text) return;
    const rr = { text }; reasons.push(rr);
    const gaveSpan = typeof e === 'object' && (e.file || e.target);
    if (gaveSpan) { const r = locateLeanSpan(e); if (r.ok) Object.assign(rr, r.span); else if (mustMap) pending.push({ desc: `the Lean span for the error "${text}" (your file=${JSON.stringify(e.file)} target=${JSON.stringify(e.target)} could not be located: ${r.why})`, sink: (s) => Object.assign(rr, s) }); }
    else if (mustMap) pending.push({ desc: `the Lean span for the error "${text}": the offending Lean fragment, or an approx anchor (approx:true) for where the missing thing belongs`, sink: (s) => Object.assign(rr, s) });
  });

  // RETRY up to RETRIES times for every unresolved required span, then ABORT. Required
  // spans are NEVER silently dropped — the run stops so you can inspect the transcript.
  for (let attempt = 1; pending.some((p) => !p._done) && attempt <= RETRIES && LAST_SID; attempt++) {
    const items = pending.map((p, k) => ({ p, k })).filter((x) => !x.p._done);
    const blocks = items.map((x) => `Item ${x.k + 1}: give ${x.p.desc}.`).join('\n');
    const dp = `Provide the required Lean spans below (retry ${attempt}/${RETRIES}). A span is {"file","target","context","approx"}: file one of [${leanFiles.join(', ')}], target a verbatim substring of that file, context a larger verbatim substring of the SAME file containing the target exactly once, "approx":true only for an anchor.\n${blocks}\nReply ONLY with JSON {"fixes": {"<item number>": {"file":...,"target":...,"context":...,"approx":false}, ...}}.`;
    try {
      const o2 = parseObject(resumeLLM(LAST_SID, dp, `judge_${tag}_retry${attempt}`)) || {};
      const fixes = (o2 && o2.fixes) || {};
      pending.forEach((p, k) => { if (p._done) return; const f = fixes[String(k + 1)]; if (!f) return; const r = locateLeanSpan(f); if (r.ok) { p.sink(r.span); p._done = true; } });
    } catch (_) {}
  }
  const unresolved = pending.filter((p) => !p._done);
  if (unresolved.length) abort(`judge_${tag}`, `${unresolved.length} required Lean span(s) unresolved after ${RETRIES} retr${RETRIES === 1 ? 'y' : 'ies'}: ${unresolved.map((p) => p.desc).join(' | ')}`);

  // de-dup box mapping spans
  const seen = new Set(); const spans = mapSpans.filter((s) => { const k = `${s.file}:${s.start}:${s.end}`; if (seen.has(k)) return false; seen.add(k); return true; });

  let verdict = v === 'faithful' ? 'ok' : v === 'unfaithful' ? 'notok' : 'unknown';
  const exactMap = spans.filter((s) => !s.approx);
  if (mustMap && verdict === 'ok' && !exactMap.length) verdict = 'notok';   // only anchored ⇒ not really formalized
  // a notok formal box must carry at least one reason, and that reason must have a span —
  // reuse the (guaranteed-present) box anchor so the synthesized error is still clickable.
  if (mustMap && verdict === 'notok' && !reasons.length) { const anchor = spans.find((s) => s.approx) || spans[0]; const rr = { text: 'Not formalized — no exact Lean counterpart.' }; if (anchor) Object.assign(rr, anchor); reasons.push(rr); }
  return { verdict, reasons, spans };
}
// Attach verdict (+per-reason spans, +box mapping spans) to a box in place. A formal box
// stores its box-level mapping as box.lean.spans (UI click jumps/highlights; entries may
// carry approx:true for anchors), or box.lean.none if even an anchor was unavailable.
// Each reason is {text, file?, start?, end?, approx?}. org boxes carry no box.lean.
function judgeBox(b, tag) {
  const { start, end } = b.pieces[0];
  const concrete = concreteOf(b.label);
  const mustMap = needsMap(concrete);
  const { verdict, reasons, spans } = judgeText(NL.slice(start, end), concrete, mustMap, tag);
  b.verdict = verdict; b.reason = reasons; b.transcript = LAST_TX;   // link box → its LLM transcript
  if (mustMap) b.lean = spans.length ? { spans } : { none: true };
}

let idc = 1; const nid = () => 'b' + idc++;
function box(labelPath, lo, hi, children = []) { return { id: nid(), label: labelPath.slice(), pieces: [{ start: lo, end: hi }], children }; }

// ---- segment the region covered by `parentBox` into labelled, located parts ---
// The LLM is offered EXACTLY the concrete label-paths the schema allows as children
// of parentBox (ISA-expanded via core.allowedLabelPaths). It returns, per part, a
// full dotted label-path + a verbatim target+context marking where the part begins;
// locate() pins each boundary to an exact offset.
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

  // Each part gives where it BEGINS as {target, context}: target = verbatim start text,
  // context = a larger verbatim window containing it (so the boundary locates uniquely
  // even if the target alone repeats). The first part always begins at `lo`.
  const resolved = parts.map((p, i) => {
    const label = (p.label && allowedSet.has(String(p.label))) ? String(p.label).split('.') : fallback;
    const target = (p.target || p.start_text || '').trim();   // start_text accepted as legacy alias
    const context = (p.context || '').trim();
    if (i === 0) return { off: lo, label };
    const r = locate(NL, target, context, lo, hi);
    return r.ok ? { off: r.start, label } : { off: null, label, target, context, why: r.why };
  });

  // RETRY unlocatable boundaries up to RETRIES times (show each failing marker's
  // target/context + why + the region it must begin in; ask for a corrected
  // target+context copied verbatim). If any boundary is STILL unlocatable, ABORT — a
  // boundary is never silently snapped, so you inspect the transcript instead.
  const letters = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
  const prevOff = (i) => { for (let j = i - 1; j >= 0; j--) if (resolved[j].off != null) return resolved[j].off; return lo; };
  const unresolvedBoundaries = () => resolved.map((r, i) => ({ r, i })).filter((x) => x.r.off === null);
  for (let attempt = 1; unresolvedBoundaries().length && attempt <= RETRIES && segSid; attempt++) {
    const items = unresolvedBoundaries();
    const blocks = items.map((a, k) => {
      const window = NL.slice(prevOff(a.i), hi);
      return `Marker ${letters[k]} — target ${JSON.stringify(a.r.target)} / context ${JSON.stringify(a.r.context)} could not be located (${a.r.why}). This part begins somewhere in:\n"""${window}"""\nGive a target (the verbatim text where this part begins) AND a larger verbatim context from the shown text that contains that target exactly once.`;
    }).join('\n\n');
    const dp = `Some boundaries could not be located verbatim (retry ${attempt}/${RETRIES}; probably a changed symbol or altered whitespace). For each marker, give corrected {"target","context"} copied EXACTLY from the shown text.\n\n${blocks}\n\nOutput ONLY a JSON object mapping each marker letter to {"target":"...","context":"..."}.`;
    let fix = {}; try { fix = parseObject(resumeLLM(segSid, dp, `segment_${tag}_retry${attempt}`)) || {}; } catch (_) {}
    items.forEach((a, k) => { const g = fix[letters[k]]; if (!g) return; const r = locate(NL, (g.target || '').trim(), (g.context || '').trim(), lo, hi); if (r.ok) { a.r.off = r.start; a.r.target = (g.target || '').trim(); } });
  }
  const stillBad = unresolvedBoundaries();
  if (stillBad.length) abort(`segment_${tag}`, `${stillBad.length} boundary/boundaries could not be located after ${RETRIES} retr${RETRIES === 1 ? 'y' : 'ies'}`);
  // clamp boundaries monotonic within [lo,hi] (all are located now; this only orders them)
  let cursor = lo;
  resolved.forEach((r) => { r.off = Math.max(cursor, Math.min(r.off, hi)); cursor = r.off; });

  const segs = [];
  for (let i = 0; i < resolved.length; i++) {
    const s = resolved[i].off, e = i + 1 < resolved.length ? resolved[i + 1].off : hi;
    if (e > s) segs.push({ lo: s, hi: e, label: resolved[i].label });
  }
  if (!segs.length) segs.push({ lo, hi, label: fallback });
  segs[0].lo = lo; segs[segs.length - 1].hi = hi;
  return segs;
}

// ---- nested deepening build: ONE growing tree, reused across levels ----------
// The whole paper is a single organizer-section box (depth 0; its allowed splits equal
// ROOT_SLOTS, so it segments exactly like the old root). "Level N" = that box expanded
// to depth N: at each level we JUDGE the current leaves, then SPLIT the splittable ones
// to form the next level. Every box is split once and judged once (when it is first a
// leaf, at its own depth); deeper levels REUSE that work. So levels truly NEST (level N
// is a refinement of level N-1) and nothing is recomputed. `--continue` re-runs this
// over a loaded tree, filling only what is missing.
let PAPER = null;                                  // the whole-paper box (tree root content)
const STATE = { levels: {} };                      // per-level stats, persisted to state.json

function walkDepth(node, d, fn) { fn(node, d); (node.children || []).forEach((c) => walkDepth(c, d + 1, fn)); }

// persist the FULL internal tree + state after every mutation (atomic) → crash-safe and
// resumable to the last completed box.
function persist() {
  if (!PAPER) return;
  const container = { id: 'root', pieces: [], children: [PAPER], links: [], lean: {} };
  const builtLevel = Object.keys(STATE.levels).length ? Math.max(...Object.keys(STATE.levels).map(Number)) : -1;
  writeJSONAtomic(path.join(RUN_DIR, 'tree.json'), container);
  writeJSONAtomic(path.join(RUN_DIR, 'state.json'), { model, mode: MODE, leanBuild: LEAN_BUILD, runTs: RUN_TS, builtLevel, updated: new Date().toISOString(), calls: SEQ, levels: STATE.levels, failures: FAILURES });
}

// judge a box once (idempotent). Marks _judged so a resume never re-judges it. Records
// the model/mode that produced the verdict (so a --allow-mismatch resume stays auditable).
function ensureJudged(b) {
  if (b._judged) return;
  if (needsVerdict(concreteOf(b.label))) { judgeBox(b, b.id); b.judgedModel = model; b.judgedMode = MODE; }
  b._judged = true; persist();
}
// split a box once (idempotent). Marks _split; a terminal label, or a split yielding
// <=1 segment, becomes a permanent leaf. Children carry their depth and must tile the
// parent exactly (segmentRegion guarantees a gapless cover).
function ensureSplit(b, d) {
  if (b._split) return;
  if (canSplit(concreteOf(b.label))) {
    const segs = segmentRegion(b, `seg_d${d}_${b.id}`);
    if (segs && segs.length > 1) {
      b.children = segs.map((s) => { const nb = box(s.label, s.lo, s.hi); nb._depth = d + 1; return nb; });
      let cur = b.pieces[0].start;
      for (const c of b.children) { if (c.pieces[0].start !== cur) throw new Error(`tiling gap under ${b.id} at ${cur}`); cur = c.pieces[0].end; }
      if (cur !== b.pieces[0].end) throw new Error(`tiling short under ${b.id}: ${cur} != ${b.pieces[0].end}`);
    }
  }
  b._split = true; persist();
}

// a CLEAN UI copy of the subtree pruned so depth-`maxd` boxes are leaves. Leaves keep
// verdict/reason/lean(spans)/transcript; internal nodes carry none (UI derives by rollup).
function viewAtDepth(node, d, maxd) {
  const leaf = d >= maxd || !(node.children && node.children.length);
  const out = { id: node.id, label: node.label, pieces: node.pieces, children: [] };
  if (leaf) {
    for (const k of ['verdict', 'reason', 'lean', 'transcript']) if (node[k] !== undefined) out[k] = node[k];
  } else {
    out.children = node.children.map((c) => viewAtDepth(c, d + 1, maxd));
  }
  return out;
}
// write the level-N view (run folder + the viewer's default findings/ location) and
// return its leaf stats.
function emitLevel(N) {
  const view = { id: 'root', pieces: [], children: [viewAtDepth(PAPER, 0, N)], links: [], lean: {} };
  writeJSONAtomic(path.join(RUN_DIR, `level${N}.json`), view);
  writeJSONAtomic(path.join(DIR, 'findings', `tree.level${N}.json`), view);
  const vc = {}; let leaves = 0, errs = 0;
  (function rec(n) {
    if (n.children && n.children.length) return n.children.forEach(rec);
    if (n.verdict !== undefined) { vc[n.verdict] = (vc[n.verdict] || 0) + 1; leaves++; if (n.verdict === 'notok') errs += Array.isArray(n.reason) ? n.reason.length : (n.reason ? 1 : 0); }
  })(view.children[0]);
  return { leaves, verdicts: vc, faithErrors: errs };
}

// restore an existing run so we can deepen it without redoing work.
function loadRun() {
  const stored = JSON.parse(fs.readFileSync(path.join(RUN_DIR, 'tree.json'), 'utf8'));
  const paper = stored.children && stored.children[0];
  if (!paper) throw new Error('loaded tree.json has no paper box');
  let maxId = 0; walkDepth(paper, 0, (n) => { const m = /^b(\d+)$/.exec(n.id); if (m) maxId = Math.max(maxId, +m[1]); });
  idc = maxId + 1;                                 // continue ids without collision
  walkDepth(paper, 0, (n, d) => { n._depth = d; }); // recompute depth fresh
  return paper;
}

function main() {
  console.error(`[run] level ${level}, model ${model}, mode ${MODE}${MODE === 'agentic' ? ` (tools: ${AGENTIC_TOOLS.join(', ')})` : ''}${CONTINUE_DIR ? ` · continue ${path.basename(RUN_DIR)}` : ''}`);
  if (CONTINUE_DIR) {
    let prev = {}; try { prev = JSON.parse(fs.readFileSync(path.join(RUN_DIR, 'state.json'), 'utf8')); } catch (_) {}
    const mism = [];
    if (prev.model && prev.model !== model) mism.push(`model ${prev.model} → ${model}`);
    if (prev.mode && prev.mode !== MODE) mism.push(`mode ${prev.mode} → ${MODE}`);
    if (prev.leanBuild !== undefined && prev.leanBuild !== LEAN_BUILD) mism.push(`leanBuild ${prev.leanBuild} → ${LEAN_BUILD}`);
    if (mism.length && !ALLOW_MISMATCH) { console.error(`[run] FATAL: --continue params differ from the run (${mism.join('; ')}). Re-run with --allow-mismatch to override.`); process.exit(1); }
    if (mism.length) console.error(`[run] WARNING: continuing with changed ${mism.join('; ')}`);
    Object.assign(STATE.levels, prev.levels || {});
    PAPER = loadRun();
    console.error(`[run] continued — reusing existing splits/verdicts, computing only what's missing`);
  } else {
    PAPER = box(['organizer-section'], 0, NL.length); PAPER._depth = 0;
  }

  // DEEPEN: for each level 0..target, judge the current depth-d leaves, emit the view,
  // then split those boxes to form depth d+1 (idempotent calls skip finished work).
  for (let d = 0; d <= level; d++) {
    const atD = []; walkDepth(PAPER, 0, (n, dd) => { if (dd === d) atD.push(n); });
    if (!atD.length) { console.error(`[run] level ${d}: no boxes at this depth (tree bottomed out) — stopping`); break; }
    atD.forEach((b) => ensureJudged(b));
    STATE.levels[d] = emitLevel(d); persist();
    const s = STATE.levels[d];
    console.error(`[run] level ${d}: ${s.leaves} judged leaf box(es), verdicts ${JSON.stringify(s.verdicts)}, ${s.faithErrors} faithfulness error(s)`);
    if (d < level) atD.forEach((b) => ensureSplit(b, d));
  }

  if (FAILURES.length) console.error(`[run] WARNING: failures ${FAILURES.join(', ')}`);
  console.error(`[run] run folder: ${path.relative(DIR, RUN_DIR)}  (tree.json, state.json, level0..${level}.json)`);
  const dump = (n, ind) => {
    const t = NL.slice(n.pieces[0].start, n.pieces[0].start + 42).replace(/\s+/g, ' ');
    const v = n.verdict !== undefined ? ` ${n.verdict === 'ok' ? '✓' : n.verdict === 'notok' ? '✗' : '?'}` : '';
    console.error(`  ${ind}${n.id} ${concreteOf(n.label)}${v} | ${t}`);
    (n.children || []).forEach((c) => dump(c, ind + '  '));
  };
  dump(PAPER, '');
}
main();
