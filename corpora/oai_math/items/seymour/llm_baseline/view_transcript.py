#!/usr/bin/env python3
# =============================================================================
# view_transcript.py -- READ-ONLY viewer for one NAIVE-baseline LLM transcript.
# =============================================================================
# Shows the EXACT prompt we sent and the EXACT reply, in a colored, scrollable
# pager — same look as the ablation-study transcript viewer. It never launches
# `claude`, never resumes, never spends budget. These transcripts hold the
# verbatim prompt + the model's FINAL reply (no hidden chain-of-thought — the
# headless CLI returns only the final answer).
#
# USAGE:
#   python3 view_transcript.py <path-to-transcript.json>   [--plain]
# The path is whatever the UI right-click shows (relative to the llm_baseline dir,
# or absolute). DEFAULT = a colored full-screen pager (less) that STARTS AT THE TOP:
#   scroll with mouse-wheel / ↑↓ / PgUp-PgDn / Space,  /=search,  g=top G=end,  q=quit.
#   To COPY text here, hold SHIFT and drag-select (the pager owns the plain mouse for
#   wheel-scroll). Or use --plain:
#   --plain  → print straight to the terminal (no pager) so plain drag-select + copy
#              work directly; good for pasting chunks elsewhere.
# =============================================================================
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

# ---- ANSI palette (same scheme as the ablation-study viewer) ----------------
C = {
    "reset": "\033[0m", "dim": "\033[2m", "bold": "\033[1m",
    "user": "\033[1;36m",       # cyan  — the prompt (what the LLM was asked)
    "assistant": "\033[1;32m",  # green — the reply
    "meta": "\033[2;37m",       # dim grey
    "tool": "\033[1;33m",       # yellow
    "hdr": "\033[1;44;97m",     # blue banner
    "sep": "\033[2;34m",
}


def col(key, s):
    return f"{C[key]}{s}{C['reset']}"


def resolve(p):
    if os.path.isabs(p) and os.path.exists(p):
        return p
    for base in (os.getcwd(), HERE):
        cand = os.path.join(base, p)
        if os.path.exists(cand):
            return cand
    return p


def _marker(line):
    """The data-block markers used by the prompts: a standalone `TEXT:` starts the
    NL source, a standalone `LEAN:` starts the Lean. Returns 'nl'/'lean' or None."""
    t = line.strip()
    if t == "TEXT:":
        return "nl"
    if t == "LEAN:":
        return "lean"
    return None


def _is_tail(line):
    """A line that ends a data block: the trailing instructions after the data
    (they start with `Reply ONLY` or a backtick, never present inside NL/Lean)."""
    t = line.strip()
    return t.startswith("Reply ONLY") or t.startswith("`")


def fold_prompt(prompt, show_nl, show_lean):
    """Render the prompt, but COLLAPSE the big data blocks to a one-line placeholder
    unless expanded. The NL source follows a `TEXT:` line and the Lean follows a
    `LEAN:` line; each block runs until the next marker or the trailing instructions.
    Everything else (the instructions) stays visible."""
    out = []
    i = 0
    lines = prompt.split("\n")
    n = len(lines)
    while i < n:
        ln = lines[i]
        kind = _marker(ln)
        if kind:
            # collect the block body: until the next marker or a tail instruction
            j = i + 1
            while j < n and not _marker(lines[j]) and not _is_tail(lines[j]):
                j += 1
            body = lines[i + 1:j]
            show = show_nl if kind == "nl" else show_lean
            out.append(col("tool", "  " + ln.strip()))
            if not show:
                nchars = sum(len(b) for b in body)
                flag = "--nl" if kind == "nl" else "--lean"
                out.append(col("meta", f"    ⟨ collapsed · {len(body)} lines, {nchars} chars · expand with {flag} (or --full) ⟩"))
            else:
                out += [col("user", "  " + b) for b in body]
            i = j
            continue
        out.append(col("user", "  " + ln))
        i += 1
    return out


def render(d, path, show_nl=False, show_lean=False):
    sep = col("sep", "─" * 78)
    folded = (not show_nl) or (not show_lean)
    lines = [
        col("hdr", " READ-ONLY TRANSCRIPT — verbatim prompt + reply · nothing is running/spent "),
        col("meta", f" file:  {path}"),
        col("meta", f" tag:   {d.get('tag','?')}      model: {d.get('model','?')}"),
        col("meta", f" when:  {d.get('when','?')}   ({d.get('ms','?')} ms)"),
    ]
    if folded:
        lines.append(col("meta", " NL source / Lean folded by default — expand with --nl, --lean, or --full"))
    lines += [sep, "",
              col("user", "❯ PROMPT") + col("meta", "  — verbatim, exactly what the LLM was asked")]
    lines += fold_prompt(d.get("prompt", "") or "(none)", show_nl, show_lean)
    lines += ["", col("assistant", "● REPLY") + col("meta", "  — verbatim, the model's final output")]
    for ln in (d.get("reply", "") or "(none)").split("\n"):
        lines.append(col("assistant", "  " + ln))
    lines += ["", sep]
    return "\n".join(lines) + "\n"


def page(text, mouse=False):
    if not sys.stdout.isatty():
        sys.stdout.write(text); return
    # Default: NO --mouse, so the terminal keeps the mouse and you can drag-select
    # + copy. --mouse trades that for wheel-scroll inside less.
    cmd = ["less", "-R"] + (["--mouse", "--wheel-lines=3"] if mouse else [])
    try:
        p = subprocess.Popen(cmd, stdin=subprocess.PIPE)
        p.communicate(text.encode("utf-8", errors="replace"))
    except (BrokenPipeError, KeyboardInterrupt):
        pass
    except FileNotFoundError:
        sys.stdout.write(text)
    finally:
        if sys.stdout.isatty() and mouse:
            sys.stdout.write("\033[?1000l\033[?1002l\033[?1003l\033[?1006l\033[?1015l\033[?1l\033>")
            sys.stdout.flush()


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if not args:
        print(__doc__); return 1
    path = resolve(args[0])
    try:
        with open(path, encoding="utf-8") as f:
            d = json.load(f)
    except FileNotFoundError:
        print(f"not found: {args[0]}"); return 1
    full = "--full" in sys.argv
    show_nl = full or "--nl" in sys.argv
    show_lean = full or "--lean" in sys.argv
    text = render(d, path, show_nl=show_nl, show_lean=show_lean)
    # Default: colored full-screen pager starting at the top. --plain dumps to the
    # terminal (for easy plain drag-select + copy).
    if "--plain" in sys.argv or not sys.stdout.isatty():
        sys.stdout.write(text)
    else:
        page(text, mouse=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
