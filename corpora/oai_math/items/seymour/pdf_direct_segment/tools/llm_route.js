// llm_route.js — the ONE place an LLM is consulted in the proof alignment, and it
// is ROUTING-ONLY. It NEVER decides faithfulness: the structural checker owns the
// verdict (a step is unfaithful iff NO candidate prop matches cleanly). When a step
// is already-unfaithful, the heuristic "closest" (max matched nodes) often points at
// the wrong prop (e.g. a rank inequality for a membership claim), which makes the
// reported divergence meaningless. So we ask a small Sonnet call ONE question: of
// these n candidate Lean propositions, which is this NL step INTENDED to correspond
// to? Output is a single index 1..n — nothing else, so it cannot rationalize a step
// into "faithful" or add noise. The verdict stays with the deterministic checker;
// this only chooses WHICH prop to report the structural divergence against.
//
// Reuses the ambient Claude Code / Bedrock auth by shelling to the `claude` CLI
// headless (`claude -p … --model claude-sonnet-5`). Returns a 0-BASED index into
// `candidates`, or null on ANY failure — the caller then falls back to the heuristic,
// so the align never breaks (and works offline / with routing disabled).
import { execFileSync } from 'child_process';

export function routeStepToProp(stepText, candidates, opts = {}) {
  if (!candidates || !candidates.length) return null;
  const model = opts.model || 'claude-sonnet-5';
  const list = candidates.map((c, i) => `${i + 1}. ${c}`).join('\n');
  const prompt = [
    'You match ONE natural-language proof step to its intended Lean counterpart.',
    'You are NOT judging correctness or faithfulness — only identifying which candidate the step is ABOUT.',
    '',
    'NL step:',
    stepText,
    '',
    'Candidate Lean propositions:',
    list,
    '',
    'Which numbered candidate is this NL step intended to correspond to?',
    'Reply with ONLY the number (a single integer, 1 to ' + candidates.length + '). No words, no punctuation.',
  ].join('\n');
  // PISTIS_LLM_DEBUG=1 → print the EXACT prompt (and later the raw reply) to stderr,
  // so the prompt actually sent can be inspected, not just the template.
  if (process.env.PISTIS_LLM_DEBUG) process.stderr.write('\n===== LLM ROUTE PROMPT (model ' + model + ') =====\n' + prompt + '\n===== END PROMPT =====\n');
  let out;
  try {
    out = execFileSync('claude', ['-p', prompt, '--model', model], {
      encoding: 'utf8', timeout: opts.timeout || 90000, stdio: ['ignore', 'pipe', 'ignore'],
    });
  } catch (_) { return null; }
  if (process.env.PISTIS_LLM_DEBUG) process.stderr.write('----- LLM raw reply: ' + JSON.stringify(out) + '\n');
  const m = (out || '').match(/\d+/);
  if (!m) return null;
  const idx = parseInt(m[0], 10);
  if (!(idx >= 1 && idx <= candidates.length)) return null;
  return idx - 1;
}
