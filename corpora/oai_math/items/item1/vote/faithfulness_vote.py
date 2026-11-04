#!/usr/bin/env python3
"""
Faithfulness A/B vote.

Shows a panel of LLM judges the natural-language proof and TWO Lean
formalizations of it, and asks which one is a more faithful rendering of the
NL argument. No bespoke metric -- just a blind pairwise preference.

Ours = the nine stepN.lean backing lemmas (verbatim) + Main.lean with the
pistis_* scaffolding rewritten to plain `have`. Theirs = _gt/MaxSupportKernel.
In cleaned mode both are reduced to plain Lean -- no pistis_*, no loc strings,
no NL literals, no comments/imports -- so neither reveals which is ours.

Fairness control: every judge sees each pair twice (ours=A / ours=B); a real
preference survives the swap. Full prompt + response is saved per call.

Usage:
  python3 faithfulness_vote.py                                    # all judges, cleaned
  python3 faithfulness_vote.py --only us.anthropic.claude-opus-4-8  # one judge
  python3 faithfulness_vote.py --list                            # print model ids, run nothing
  python3 faithfulness_vote.py --raw                             # don't strip anything
  python3 faithfulness_vote.py --reps 3                          # 3x per orientation
"""
import os, re, json, argparse, concurrent.futures as cf
import requests

HERE = os.path.dirname(os.path.abspath(__file__))
ITEM = os.path.dirname(HERE)
DATA = os.path.join(ITEM, "data")

MAIN_PATH   = os.path.join(ITEM, "Main.lean")
STEP_PATHS  = [os.path.join(ITEM, f"step{k}.lean") for k in range(1, 10)]
THEIRS_PATH = os.path.join(ITEM, "_gt", "MaxSupportKernel.lean")

REGION = os.environ.get("AWS_REGION", "us-east-1")
TOKEN  = os.environ["AWS_BEARER_TOKEN_BEDROCK"]

# The exact Bedrock model ids called. The id is the name -- no shorthand, no
# tags. Pass one verbatim to --only to run just that model. Confirmed invokable
# on this account; current-gen Claude 5.x / GPT-6.x are listed in Bedrock but
# every invoke 404s, so they are absent until console model access is enabled.
MODELS = [
    "us.anthropic.claude-opus-4-8",
    "openai.gpt-oss-120b-1:0",
    "minimax.minimax-m2.5",
    "deepseek.v3.2",
    "mistral.mistral-large-3-675b-instruct",
    "qwen.qwen3-32b-v1:0",
    "google.gemma-3-27b-it",
]


def strip_comments(text: str) -> str:
    """Remove line (--) and block (/- -/) comments, imports, set_option, open."""
    text = re.sub(r"/-[\s\S]*?-/", "", text)
    out = []
    for line in text.splitlines():
        s = line.strip()
        if s.startswith(("import ", "set_option ", "open ")):
            continue
        line = re.sub(r"--.*$", "", line)      # trailing / full-line comments
        out.append(line)
    text = "\n".join(out)
    return re.sub(r"\n{3,}", "\n\n", text).strip()


def depistify(main_src: str) -> str:
    """Rewrite Main.lean's pistis_* scaffolding into plain Lean:
       pistis_segment "loc" r"nl" (name : T) := by body   ->   have name : T := by body
       pistis_assumption "loc" r"nl" (name : T) := by body ->   have name : T := by body
       pistis_intro "loc" r"nl"                            ->   (dropped)
    No pistis_*, no loc strings, no NL r"..." literals, no assumption tags remain."""
    s = r'r?"(?:[^"\\]|\\.)*"'          # a "loc" or r"nl" string literal
    # pistis_intro "loc" r"..."  -> remove whole call
    main_src = re.sub(rf'pistis_intro\s+{s}\s+{s}', "", main_src)
    # pistis_segment/assumption "loc" r"nl" (name : TYPE) :=  -> have name : TYPE :=
    # TYPE may contain nested parens; the balanced terminator is ") :=" (":=" never
    # appears inside a claim type), so a lazy match to ")\s*:=" is exact.
    main_src = re.sub(
        rf'pistis_(?:segment|assumption)\s+{s}\s+{s}\s*\(\s*(.*?)\s*\)\s*:=',
        r'have \1 :=', main_src, flags=re.DOTALL)
    return main_src


def load(raw: bool):
    nl_stmt  = open(os.path.join(DATA, "nl_statement.txt")).read().strip()
    nl_proof = open(os.path.join(DATA, "nl_proof.txt")).read().strip()

    # OURS = the nine backing lemmas (verbatim, they compile) + Main with the
    # pistis_* scaffolding rewritten to `have`. The judge sees the real bodies.
    helpers = "\n\n".join(open(p).read() for p in STEP_PATHS)
    main    = depistify(open(MAIN_PATH).read())
    ours    = helpers + "\n\n" + main
    theirs  = open(THEIRS_PATH).read()

    if not raw:
        ours, theirs = strip_comments(ours), strip_comments(theirs)
    return nl_stmt, nl_proof, ours, theirs


PROMPT = """You are grading two formalizations of a mathematical proof in the Lean theorem prover.

A formalization is FAITHFUL if its structure mirrors the natural-language (NL) proof: the same intermediate steps, under the same assumptions, in the same order -- not merely a proof that reaches the same conclusion by some other route.

Here is the NL statement being proved:
---
{stmt}
---

Here is the NL proof whose reasoning the Lean code is supposed to mirror:
---
{proof}
---

FORMALIZATION A:
```lean
{a}
```

FORMALIZATION B:
```lean
{b}
```

Which formalization follows the natural-language proof's reasoning more faithfully -- same steps, same assumptions, same order? If they are genuinely indistinguishable, you may say TIE, but only then.

Respond with ONLY a JSON object on a single line, no prose, no code fence:
{{"winner": "A" | "B" | "TIE", "reason": "<one sentence>"}}"""


def converse(model_id: str, prompt: str):
    """Return (text, full_response_json). text is the assistant's text blocks
    joined (reasoningContent blocks from DeepSeek/gpt-oss are skipped)."""
    url = f"https://bedrock-runtime.{REGION}.amazonaws.com/model/{model_id}/converse"
    hdr = {"Authorization": f"Bearer {TOKEN}", "Content-Type": "application/json"}

    def post(with_temp: bool):
        cfg = {"maxTokens": 1200}
        if with_temp:
            cfg["temperature"] = 0           # determinism where it's accepted
        body = {"messages": [{"role": "user", "content": [{"text": prompt}]}],
                "inferenceConfig": cfg}
        return requests.post(url, headers=hdr, data=json.dumps(body), timeout=180)  # type: ignore[arg-type]

    r = post(with_temp=True)
    # some models (e.g. Opus 4.8) deprecate `temperature`; retry without it
    if r.status_code == 400 and "temperature" in r.text:
        r = post(with_temp=False)
    r.raise_for_status()
    full = r.json()
    blocks = full["output"]["message"]["content"]
    text = "".join(b.get("text", "") for b in blocks).strip()
    return text, full


def parse_winner(text: str):
    m = re.search(r'\{[^{}]*"winner"[^{}]*\}', text, re.DOTALL)
    if not m:
        return None, text[:160]
    try:
        obj = json.loads(m.group(0))
    except Exception:
        return None, text[:160]
    w = str(obj.get("winner", "")).strip().upper()
    if w not in ("A", "B", "TIE"):
        return None, text[:160]
    return w, obj.get("reason", "")[:200]


def save_transcript(tdir, model_id, rep, ours_is_a, prompt, raw, full, result):
    orient = "oursA" if ours_is_a else "oursB"
    safe = re.sub(r"[^A-Za-z0-9._-]", "_", model_id)
    path = os.path.join(tdir, f"{safe}.rep{rep}.{orient}.json")
    json.dump({
        "model_id": model_id, "rep": rep,
        "ours_is_a": ours_is_a, "A": "ours" if ours_is_a else "theirs",
        "prompt": prompt, "response_text": raw,
        "response_full": full, "result": result,
    }, open(path, "w"), indent=2, ensure_ascii=False)


def one_call(model_id, rep, nl_stmt, nl_proof, ours, theirs, ours_is_a, tdir):
    a, b = (ours, theirs) if ours_is_a else (theirs, ours)
    prompt = PROMPT.format(stmt=nl_stmt, proof=nl_proof, a=a, b=b)
    raw, full = "", None
    try:
        raw, full = converse(model_id, prompt)
    except Exception as e:
        result = {"ok": False, "err": str(e)[:160], "ours_is_a": ours_is_a}
        save_transcript(tdir, model_id, rep, ours_is_a, prompt, raw, full, result)
        return result
    w, reason = parse_winner(raw)
    if w is None:
        result = {"ok": False, "err": "unparseable: " + reason, "ours_is_a": ours_is_a}
        save_transcript(tdir, model_id, rep, ours_is_a, prompt, raw, full, result)
        return result
    if w == "TIE":
        verdict = "TIE"
    elif (w == "A") == ours_is_a:
        verdict = "OURS"
    else:
        verdict = "THEIRS"
    result = {"ok": True, "verdict": verdict, "reason": reason, "ours_is_a": ours_is_a}
    save_transcript(tdir, model_id, rep, ours_is_a, prompt, raw, full, result)
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--raw", action="store_true", help="do not strip comments/NL literals")
    ap.add_argument("--reps", type=int, default=1, help="repeats per orientation")
    ap.add_argument("--only", default=None,
                    help="run only this exact model id (must match MODELS verbatim)")
    ap.add_argument("--list", action="store_true", help="print the model ids and exit")
    args = ap.parse_args()

    global MODELS
    if args.list:
        for mid in MODELS:
            print(mid)
        return
    if args.only:
        if args.only not in MODELS:
            print(f"unknown model id {args.only!r}; one of:")
            for mid in MODELS:
                print("  " + mid)
            return
        MODELS = [args.only]

    nl_stmt, nl_proof, ours, theirs = load(args.raw)
    mode = "RAW" if args.raw else "CLEANED"

    tdir = os.path.join(HERE, f"transcripts_{mode.lower()}")
    os.makedirs(tdir, exist_ok=True)
    # the exact inputs every judge saw, saved alongside the per-call transcripts
    open(os.path.join(tdir, "_prompt_template.txt"), "w").write(PROMPT)
    open(os.path.join(tdir, "_ours.lean"), "w").write(ours)
    open(os.path.join(tdir, "_theirs.lean"), "w").write(theirs)

    print(f"=== Faithfulness vote  [{mode}]  ours=Main.lean  theirs=_gt/MaxSupportKernel.lean ===")
    print(f"ours {len(ours)} chars, theirs {len(theirs)} chars, {len(MODELS)} judges, "
          f"{2*args.reps} calls each (A/B swap)")
    print(f"full transcripts -> {tdir}\n")

    jobs = []
    for mid in MODELS:
        for rep in range(args.reps):
            for ours_is_a in (True, False):
                jobs.append((mid, rep, ours_is_a))

    results = {mid: [] for mid in MODELS}
    with cf.ThreadPoolExecutor(max_workers=10) as ex:
        futs = {ex.submit(one_call, mid, rep, nl_stmt, nl_proof,
                          ours, theirs, a, tdir): mid
                for (mid, rep, a) in jobs}
        for fut in cf.as_completed(futs):
            results[futs[fut]].append(fut.result())

    tot = {"OURS": 0, "THEIRS": 0, "TIE": 0}
    print(f"{'MODEL ID':44} {'OURS':>5} {'THEIRS':>7} {'TIE':>4} {'ERR':>4}   verdict")
    print("-" * 90)
    rows = []
    for mid in MODELS:
        rs = results[mid]
        c = {"OURS": 0, "THEIRS": 0, "TIE": 0}
        err = 0
        for r in rs:
            if r["ok"]:
                c[r["verdict"]] += 1
            else:
                err += 1
        for k in tot:
            tot[k] += c[k]
        if c["OURS"] > c["THEIRS"] and c["THEIRS"] == 0 and c["OURS"] > 0:
            v = "OURS (both orientations)"
        elif c["OURS"] > c["THEIRS"]:
            v = "OURS"
        elif c["THEIRS"] > c["OURS"]:
            v = "THEIRS"
        elif c["OURS"] == c["THEIRS"] == 0:
            v = "-"
        else:
            v = "split"
        print(f"{mid:44} {c['OURS']:>5} {c['THEIRS']:>7} {c['TIE']:>4} {err:>4}   {v}")
        rows.append({"model": mid, **c, "err": err, "verdict": v, "detail": rs})
    print("-" * 90)
    n = sum(tot.values())
    pct = (100 * tot["OURS"] / n) if n else 0
    print(f"{'TOTAL':44} {tot['OURS']:>5} {tot['THEIRS']:>7} {tot['TIE']:>4}")
    print(f"\nAcross {len(MODELS)} models: OURS preferred in {tot['OURS']}/{n} "
          f"non-error votes ({pct:.0f}%), THEIRS {tot['THEIRS']}, TIE {tot['TIE']}.")

    out = os.path.join(HERE, f"vote_{mode.lower()}.json")
    json.dump({"mode": mode, "totals": tot, "rows": rows}, open(out, "w"), indent=2)
    print(f"\nwrote {out}")


if __name__ == "__main__":
    main()
