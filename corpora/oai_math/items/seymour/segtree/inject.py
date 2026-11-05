#!/usr/bin/env python3
r"""Inject {\color{..} ...} highlights into the tex at (file, start, end) spans
and compile the whole paper.

DATA MODEL: a box is {file, start, end} where start/end are char offsets into
that ONE untouched source file (src/<file>). No concatenation, no combined
offsets, no mapping layer. Nesting = containment within the same file.

To show highlights in the PDF we:
  1. copy every src file into a work dir (verbatim),
  2. for each box, wrap src[start:end] of its file in {\color{<c>} ... },
  3. compile main.tex (which \input's 00..05) with one lualatex/pdflatex pass
     (the .aux is prebuilt so refs resolve), and
  4. return the PDF.

Validity (block-at-creation) is structural and per file: the span must be
well-formed to wrap (balanced braces, not starting/ending inside math, not
closing a group it did not open). A clean span is exactly one that compiles when
wrapped, so no compile is needed to validate.
"""
import os
import re
import shutil
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "src")                     # verbatim, self-contained copy
WORK = "/tmp/segtree_work"
OUTDIR = "/tmp/segtree_out"
PDF = os.path.join(OUTDIR, "main.pdf")


def list_files(ext=None):
    """Every file under src/, as relative POSIX paths (folders preserved),
    sorted. ext filters by extension (e.g. '.tex')."""
    out = []
    for root, dirs, names in os.walk(SRC):
        dirs.sort()
        for n in names:
            rel = os.path.relpath(os.path.join(root, n), SRC).replace(os.sep, "/")
            if ext is None or rel.endswith(ext):
                out.append(rel)
    return sorted(out)


# every .tex file is a potential highlight target; everything is copied verbatim
TEX_FILES = list_files(".tex")
ALL_FILES = list_files()


def read_file(name):
    with open(os.path.join(SRC, name)) as f:
        return f.read()


# ---------------------------------------------------------------- validity
def scan_states(text):
    """Per-position brace depth D and math flag M (len == len(text)+1)."""
    depth = math = 0
    D = []
    M = []
    i = 0
    n = len(text)
    while i < n:
        D.append(depth); M.append(math)
        ch = text[i]
        if ch == "\\" and i + 1 < n:
            nxt = text[i + 1]
            if nxt in "([":
                math += 1; D.append(depth); M.append(math); i += 2; continue
            if nxt in ")]":
                math -= 1; D.append(depth); M.append(math); i += 2; continue
            D.append(depth); M.append(math); i += 2; continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
        elif ch == "$":
            if text[i + 1:i + 2] == "$":
                math ^= 1; D.append(depth); M.append(math); i += 2; continue
            math ^= 1
        i += 1
    D.append(depth); M.append(math)
    return D, M


_STATE_CACHE = {}
def span_is_clean(file, s, e):
    if file not in TEX_FILES:
        return False, "not a highlightable tex file"
    if file not in _STATE_CACHE:
        _STATE_CACHE[file] = scan_states(read_file(file))
    D, M = _STATE_CACHE[file]
    if not (0 <= s < e <= len(D) - 1):
        return False, "out of range"
    if M[s] != 0 or M[e] != 0:
        return False, "starts or ends inside math"
    if D[s] != D[e]:
        return False, "brace-unbalanced across the span"
    base = D[s]
    for k in range(s, e):
        if D[k] < base:
            return False, "span closes a group it did not open"
    # environments: \begin{env}/\end{env} must be balanced WITHIN the span — a
    # dangling \begin or \end (span cuts across a figure/equation/etc. boundary)
    # is brace-balanced yet still breaks LaTeX, so reject it here.
    ok, why = _env_balanced(read_file(file), s, e)
    if not ok:
        return False, why
    return True, "ok"


_ENV_RE = re.compile(r"\\(begin|end)\s*\{([^}]*)\}")
def _env_balanced(text, s, e):
    stack = []
    for m in _ENV_RE.finditer(text, s, e):
        if m.end() > e:
            break
        kind, env = m.group(1), m.group(2)
        if kind == "begin":
            stack.append(env)
        else:  # end
            if not stack:
                return False, f"span ends an environment ({env}) it did not open"
            if stack[-1] != env:
                return False, f"environment mismatch (\\end{{{env}}} vs \\begin{{{stack[-1]}}})"
            stack.pop()
    if stack:
        return False, f"span opens an environment ({stack[-1]}) it does not close"
    return True, "ok"


def validate_span(file, s, e):
    return span_is_clean(file, s, e)


# ---------------------------------------------------------------- compile
# (compiled with pdflatex — no lualatex / lua-ul needed anymore)

# Colour override, text + math alike. A plain \color declaration cascades into
# inline AND display maths (verified), so no \everymath tricks are needed — those
# broke align's \halign. Document default is grey (set after \begin{document});
# \seg{colour}{content} overrides within a group (reverts after), and nesting
# just overrides again.
SEG_PREAMBLE = (
    "\\usepackage{xcolor}\n"
    "\\definecolor{seggrey}{gray}{0.62}\n"
    "\\newcommand{\\seg}[2]{{\\color{#1}#2}}\n"
)

_WORK_READY = False
def ensure_work():
    """Verbatim work copy of all source files; main.tex patched for lualatex +
    lua-ul highlighting; aux/bbl prebuilt so one pass resolves references.

    Idempotent and self-healing: we re-check that the work dir + prebuilt aux
    actually exist on disk, not just a cached flag — so a wiped /tmp can never
    leave the server returning 'no such file' 500s.
    """
    global _WORK_READY
    aux = os.path.join(OUTDIR, "main.aux")
    if _WORK_READY and os.path.exists(os.path.join(WORK, "main.tex")) and os.path.exists(aux):
        return
    # copy the ENTIRE self-contained src/ tree verbatim, preserving folders
    # (figures/ included). No external path dependency.
    if os.path.exists(WORK):
        shutil.rmtree(WORK)
    shutil.copytree(SRC, WORK)
    os.makedirs(OUTDIR, exist_ok=True)
    # prebuild aux/bbl + synctex (for PDF->source reverse mapping) with latexmk.
    subprocess.run(["latexmk", "-pdf", "-synctex=1", "-interaction=nonstopmode",
                    f"-output-directory={OUTDIR}", "main.tex"],
                   cwd=WORK, capture_output=True, text=True)
    _WORK_READY = True




def _hexkey(col):
    """Normalize a #RRGGBB (or RRGGBB) string to 6 uppercase hex chars."""
    return col.lstrip("#")[-6:].upper()


def _write_highlighted(segs):
    r"""Write work copies, wrapping each selected segment in \seg{colour}{...}.

    segs: a flat list of NON-OVERLAPPING segments [{file, s, e, color}] where
    color is '#RRGGBB'. The frontend pre-splits boxes at their boundaries and
    gives each piece one colour; the backend just wraps each piece. A segment
    must be a clean span (span_is_clean) or it is dropped.

    Colouring is a COLOUR OVERRIDE, not a background: the document default is
    grey (set after \begin{document}); \seg overrides to the span's colour, text
    and maths alike. Nothing changes layout.
    """
    by_file = {}
    colors = {}                       # hexkey -> itself (unique set)
    for g in segs:
        f = g.get("file")
        if f not in TEX_FILES:
            continue
        if not span_is_clean(f, g["s"], g["e"])[0]:
            continue
        key = _hexkey(g["color"])
        colors[key] = key
        by_file.setdefault(f, []).append((g["s"], g["e"], key))

    defs = "".join(f"\\definecolor{{seg{k}}}{{HTML}}{{{k}}}\n" for k in colors)

    for f in TEX_FILES:
        text = read_file(f)                       # always pristine; offsets valid
        segments = sorted(by_file.get(f, []), key=lambda t: t[0])
        out = []
        prev = 0
        for (s, e, key) in segments:
            if s < prev:                          # safety: skip stray overlap
                continue
            out.append(text[prev:s])
            out.append("\\seg{seg" + key + "}{")
            out.append(text[s:e])
            out.append("}")
            prev = e
        out.append(text[prev:])
        body = "".join(out)
        if f == "main.tex":                       # preamble patch lives here only
            body = _apply_preamble(body, defs)
        open(os.path.join(WORK, f), "w").write(body)


def _apply_preamble(m, defs):
    m = m.replace("\\usepackage{microtype}", SEG_PREAMBLE + defs + "\\usepackage{microtype}", 1)
    # The whole paper is ALWAYS grey by default (text + maths via \color, TikZ via
    # the \tikzset); the only black/coloured things are the spans we select, which
    # override via \seg. One rule, no focus/non-focus branching.
    m = m.replace("\\begin{document}",
                  "\\begin{document}\n\\color{seggrey}\n"
                  "\\tikzset{every picture/.style={color=seggrey}}\n"
                  # captions sit in a float box set OUTSIDE the body colour scope;
                  # this hook starts every float (incl. its \\caption) in grey.
                  "\\makeatletter\\g@addto@macro\\@floatboxreset{\\color{seggrey}}"
                  "\\makeatother", 1)
    return m


def compile_tree(segs):
    """Inject all segments, one pdflatex pass (with synctex for PDF->source
    reverse mapping). Returns (ok, pdf_or_None, log)."""
    ensure_work()
    _write_highlighted(segs)
    r = subprocess.run(["pdflatex", "-synctex=1", "-interaction=nonstopmode",
                        "-halt-on-error", f"-output-directory={OUTDIR}", "main.tex"],
                       cwd=WORK, capture_output=True, text=True)
    ok = os.path.exists(PDF) and r.returncode == 0
    return ok, (PDF if ok else None), r.stdout[-3000:]


def reverse_sync(page, x, y):
    """SyncTeX reverse: a PDF point (page, x,y in PDF points, top-left origin) ->
    (file, line) in the source, or None. Rough (line-level) by nature."""
    synctex = os.path.join(OUTDIR, "main.synctex.gz")
    if not os.path.exists(synctex):
        return None
    out = subprocess.run(
        ["synctex", "edit", "-o", f"{page}:{x}:{y}:{PDF}"],
        capture_output=True, text=True).stdout
    inp = line = None
    for ln in out.splitlines():
        if ln.startswith("Input:"):
            inp = ln[len("Input:"):]
        elif ln.startswith("Line:"):
            line = int(ln[len("Line:"):])
            break
    if not inp or line is None:
        return None
    # map the WORK path back to a src-relative file
    rel = os.path.relpath(inp, WORK).replace(os.sep, "/") if inp.startswith(WORK) else os.path.basename(inp)
    return {"file": rel, "line": line}


if __name__ == "__main__":
    # self-check on real offsets, no magic
    intro = read_file("00-introduction.tex")
    i = intro.index("oriented graph")
    print("prose span clean:", validate_span("00-introduction.tex", i, i + 14))
    j = intro.index("\\(v\\)")
    print("into-math rejected:", validate_span("00-introduction.tex", j + 1, j + 3))
    mn = read_file("main.tex")
    a = mn.index("We prove"); e = mn.index("positively.") + 11
    mid = a + (e - a) // 2
    ok, pdf, log = compile_tree([
        {"file": "main.tex", "s": a, "e": mid, "color": "#20C552"},
        {"file": "main.tex", "s": mid, "e": e, "color": "#8120C5"},
    ])
    print("lua-ul highlight compile:", ok, "->", pdf)
    if not ok:
        for ln in log.splitlines():
            if ln.startswith("!"):
                print("ERR:", ln)
