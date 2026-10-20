"""The align-then-label UNITS of a Pistis item, read off its `Main.lean` + `split.json`.

The faithfulness-dataset model is per-STATEMENT: one datapoint = one (T_F, T_N) pair, annotated
align-then-label. A Pistis item is a whole PROOF, so it decomposes into many such pairs — one per
place where the formalization claims to say what the prose says:

    statement     the item's `nl_statement.txt`        <-> the Lean theorem statement
    seg-<loc>     one `pistis_segment`'s ASSERT         <-> that segment's Lean claim
    asm-<loc>-<k> one of its `assumptions`             <-> that `@pistis_assumption`'s TYPE

Every unit is derived, never hand-maintained: edit `Main.lean` or `split.json` and the units move with
it. `gen_datapoints.py` turns units into `artifacts/` skeletons; `ui/proof_pane.js` renders them in
place in the proof, each one clicking through to its align-then-label view.

Targets, per unit kind
----------------------
`statement` gets the real thing: the item's header (imports / opens / `variable`s / any supporting
`def`) plus the theorem signature with a `sorry` body, flattened by `tf_norm.normalize_tf` exactly as
upstream does. `import Pistis` and the Pistis `set_option` are dropped — they exist only so the
`pistis_*` tactics elaborate, and are not part of the formal statement.

`seg-*` gets the CLAIM, and nothing else: exactly the proposition written inside `(stepK : …)`, with
the binder name dropped and whitespace collapsed. Not the surrounding tactic, not the `:= by` body,
not the lines above it, and not a synthetic `theorem` with the binders re-stated. By definition the
segment ASSERTS its claim and only its claim, so that proposition is the whole of what the sentence is
being judged against; `check_targets.py` fails if a stored `T_F` is anything else.

A segment's NL target is the OTHER HALF of that rule, and it is not the whole sentence
--------------------------------------------------------------------------------------
The paper gives each segment `s_i` two mappings: `assumps(s_i)`, a set of substrings, and
`assert(s_i)`, what is left — the thing the sentence puts forward on its own authority. Atomicity is
that there is ONE of the latter; `formal(assert(s_i))` is the claim, and each assumption gets a `ϕ_k`
of its own. So the prose a segment's claim is judged against is the segment MINUS its assumptions,
and `segment_nl_target` computes exactly that: each `assumptions` substring is cut out and a single
`…` (`GAP`) left where it stood.

T_N was the whole sentence before this, which quietly put the premises inside the target of the
claim that consumes them. Nothing in the claim can answer them — the claim is the `assert` — so they
could only take ⊥ edges, and a ⊥ edge says "the formalization does not say this". That is false
twice over: the premise IS formalized, in the marker's TYPE, and *this* unit was never the place
that formalization was supposed to appear. Worse, the pressure it creates is to widen the claim into
a conjunction so the premises have something to align against, which is precisely the Atomicity
break `check_main.py` check 6 now exists to stop (`items/item1` segment 1.7 shipped that way).

The `GAP` is kept rather than closed up, and it carries a span and a ⊥ edge like any other
character: a reader of the segment's unit should see WHERE a premise was lifted out, and follow it to
the `asm-*` unit that holds it. Dropping it silently would make the sentence read as though the prose
never stated the premise at all.

`asm-*` is that unit: `T_N` is the assumption clause, verbatim as `split.json` quotes it out of the
segment, and `T_F` is the Lean type on its `-- @pistis_assumption ("…", TYPE)` marker. This is the
pair the paper's Atomic Faithfulness condition quantifies over (`∀ a ∈ assumps(s_i), formal(a) is
faithful`), and until these units existed it was the one condition with nothing on disk to check.
Assumption units carry no `C_F`: a marker introduces nothing, it consumes.

What the sentence INTRODUCES is formal context. "For a nonzero real τ, the matrix D_τ = D + τ e_s e_jᵀ
is still supported on T" is formalized partly by the `obtain`/`set` lines above the tactic, and a
sentence that opens a reductio ("Suppose instead that …") by the `have h : ¬P := by intro hp` it sits
inside. Those lines are not part of the claim, so they are not part of `T_F`; they are `C_F` items,
and the prose that introduces the object is linked to them.

Formal context (`C_F` seeds)
----------------------------
A segment's `C_F` is what THIS sentence introduces: every record between its `pistis_*` tactic and
the previous one. Nothing else. For seg-1.2 that is the `obtain` and the `set`; for most sentences it
is empty, because most sentences introduce nothing.

**A record is a QUOTE of the proof — the clause as written, and the line(s) it is written on.** Not a
reconstructed `name : type`. The difference is not cosmetic: `intro hsuppose1` introduces a
hypothesis whose type is written on the `have` above it, and spelling that out as
`hsuppose1 : x j * y s ≠ 0` puts a string in the datapoint that appears nowhere in the file. A reader
following the citation does not find it, and the annotation stops being evidence about the
formalization and becomes evidence about the seeder. So every record's text is sliced out of a line
and then CHECKED against that line before it is emitted (`_quote`), which makes a paraphrase
impossible here rather than merely discouraged. `check_verbatim.py` is the same check from outside.

The clause is also the right unit of context, not the name: `obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ ≠ 0` is one
thing the proof does, and the prose's "for a nonzero real τ" is one thing the prose says. Splitting
it into `τ : ℝ` and `hτ : τ ≠ 0` was two paraphrases where the file has one sentence.

It is tempting to add what the claim needs in order to be READ — `x j * y s ≠ 0` is unintelligible
without `x : J → ℝ` — but that rule has no floor. `x : J → ℝ` needs `ℝ`, which needs the field
axioms, which need ⋯; stopping at the ones that happen to live in `Main.lean` is an artefact of
`_ambient` reading one file, not a principle. So the line is drawn where the rest of this module
draws it: a unit holds what its own sentence says. The theorem's binders are the `statement` unit's
business, and that unit judges each of them against the prose that actually introduces it, once,
instead of nine times over against prose that merely uses the name.

The consequence worth noticing: every `C_F` item is now linked to the clause that introduces it, so
a ⊥ edge out of `C_F` does not arise. An item nothing refers to is a sign the seed is wrong, not
something to paper over with ⊥.

`_ambient` still scans the whole file (`variable` groups, top-level `def`s, the theorem's binders,
`set`/`obtain`/`have`/`intro` introductions, each earlier `stepK`), because the line each clause sits
on is what the range filter needs. A best-effort seed, not a guarantee: the labeler adds or edits
`C_F` items in the UI.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

from tf_norm import normalize_tf, strip_comments
from alignment_data import _utf16_len

PISTIS_SCRIPTS = Path(__file__).resolve().parents[3] / "scripts"
if str(PISTIS_SCRIPTS) not in __import__("sys").path:
    __import__("sys").path.insert(0, str(PISTIS_SCRIPTS))
# `_TAC` is borrowed rather than re-declared: `source_anchors` locates the very constructs
# `parse_main` reads, and a second copy of that pattern here could silently drift from the one the
# checkers use.
from pistis_lean import (                              # noqa: E402
    parse_main, parse_assumptions, read_string_literal, _TAC as _TACTIC_RE,
)

# What a removed assumption leaves behind in a segment's NL target. U+2026, one character, and it
# occurs in no `data/nl_*.txt` in either corpus — so it cannot be confused with the prose, and
# `check_verbatim.py` can split a gapped target on it without ambiguity.
GAP = "…"

# Lines that exist only to make the `pistis_*` tactics elaborate, not part of the formal statement.
_SCAFFOLD_LINE = re.compile(r"^\s*(import\s+Pistis|set_option\s+linter\.unusedTactic)\b")

_OPEN = "([{⦃⟨"
_CLOSE = ")]}⦄⟩"
_PAIR = dict(zip(_OPEN, _CLOSE))

def _split_groups(s: str) -> tuple[list[str], str]:
    """Split a binder list into balanced bracket groups, stopping at the first TOP-LEVEL `:`.

    Returns (groups, rest) where `rest` is everything from that `:` on (a theorem's goal) or `""`.
    Nested brackets and string literals are skipped, so `(hsj : (s, j) ∈ T)` stays one group.
    """
    groups: list[str] = []
    stack: list[str] = []
    start, i, n = None, 0, len(s)
    while i < n:
        c = s[i]
        if c == '"':
            i += 1
            while i < n and s[i] != '"':
                i += 2 if s[i] == "\\" else 1
            i += 1
            continue
        if not stack and c == ":":
            return groups, s[i:]
        if c in _OPEN:
            if not stack:
                start = i
            stack.append(_PAIR[c])
            i += 1
            continue
        if stack and c == stack[-1]:
            stack.pop()
            if not stack and start is not None:
                groups.append(s[start:i + 1])
                start = None
        i += 1
    return groups, ""


def _collapse(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def _quote(lines: list[str], text: str, start: int = 1, span: int = 8) -> dict | None:
    """One `C_F` record for `text`, or None if the file does not say it.

    `text` must occur in `lines` (whitespace-insensitively, since a binder or a claim may be written
    across several of them); the record's citation is then the TIGHTEST line range containing it —
    `items/item1/Main.lean:47`, or `…:11-12` for a declaration spanning two lines. Searching from
    `start` keeps the scan in source order, so a clause repeated later in the proof is cited where it
    was read, not where it next appears.

    Deriving the citation by LOCATING the text is the point. A reader that slices its records out of
    the source can still get the line wrong, and one that builds them out of pieces can be wrong
    about the words themselves; here the words are the search key, so a record that is not a quote of
    the file cannot acquire a citation at all — it comes back None and is dropped. That is also why
    this returns a record rather than a range: there is nothing to emit without one.
    """
    want = _collapse(text)
    if not want:
        return None
    for hi in range(start, len(lines) + 1):                  # smallest end first …
        for lo in range(hi, max(start, hi - span) - 1, -1):  # … then the latest start that works
            if want in _collapse(" ".join(lines[lo - 1:hi])):
                loc = f"{lo}-{hi}" if hi > lo else f"{lo}"
                return {"signature": want, "source": loc, "line": lo}
    return None


def _code_lines(src: str) -> list[str]:
    """One entry per LINE of `src`, with the comments blanked out.

    Same comment grammar as `tf_norm.strip_comments` (nested `/- -/`, `--` to end of line), but
    line-preserving, which `strip_comments` is not: it drops the newlines INSIDE a block comment, so
    everything below a `/-- … -/` spanning two lines shifts up by one. An index into that output is
    then not a line number, and every `C_F` item below the comment cites a line it is not quoting —
    in item1 that put `hτ`'s citation on a comment and `hDτ`'s on the `obtain` above its `set`.
    `check_citations.py` is the gate that keeps this honest.

    `tf_norm` is vendored verbatim, hence a second scanner here rather than a flag over there.
    """
    out: list[list[str]] = [[] for _ in range(src.count("\n") + 1)]
    i, n, depth, line = 0, len(src), 0, 0
    while i < n:
        two = src[i:i + 2]
        if src[i] == "\n":                          # never code; always advances the line
            line += 1
            i += 1
        elif depth:
            if two == "/-":
                depth += 1
                i += 2
            elif two == "-/":
                depth -= 1
                i += 2
            else:
                i += 1
        elif two == "/-":
            depth += 1
            i += 2
        elif two == "--":
            j = src.find("\n", i)
            i = n if j < 0 else j
        else:
            out[line].append(src[i])
            i += 1
    if src.endswith("\n"):
        out.pop()                                   # a trailing newline is not a line of its own
    return ["".join(ln) for ln in out]


def _ambient(src: str, path: str) -> list[dict]:
    """Every clause in `Main.lean` that brings something into scope, in source order.

    Each record is `{signature, source, line}`, where `signature` is the clause QUOTED from the file
    (the key keeps its upstream name, which the vendored labeler reads) and `line` is a RAW line
    number — what the gutter shows — so a unit can take only what precedes it. There is no `name`
    field: the clause already says which names it binds, and a `name : type` beside it was a second,
    paraphrased way of saying the same thing. Best-effort by design (see the module docstring).

    Everything here goes through `_quote`, so a record is either words that are in the file or no
    record at all.
    """
    out: list[dict] = []
    lines = _code_lines(src)                        # docstrings/comments never introduce a name

    def take(text: str, start: int = 1, at: int | None = None) -> None:
        rec = _quote(lines, text, start)
        if rec:                                     # None = the file does not say it; say nothing
            out.append({**rec, "source": f"{path}:{rec['source']}",
                        "line": rec["line"] if at is None else at})

    for i, raw in enumerate(lines):
        line = raw.strip()
        if not line:
            continue
        if line.startswith("variable "):
            # one record per binder GROUP: `{I J : Type*}` is how the file writes it, and splitting it
            # into `I : Type*` / `J : Type*` would be writing something else.
            for g in _split_groups(line[len("variable "):])[0]:
                take(g, i + 1)
            continue
        # a supporting top-level definition: the whole declaration, however many lines it takes
        if re.match(r"(?:noncomputable\s+)?(?:def|abbrev)\s+[^\s({\[:]+", line):
            decl = [line]
            j = i + 1
            while j < len(lines) and lines[j][:1].isspace() and lines[j].strip():
                decl.append(lines[j].strip())
                j += 1
            take(" ".join(decl), i + 1)
            continue
        # The tactics that put something in scope. Each is quoted up to the proof that follows, since
        # `:= ⟨1, one_ne_zero⟩` / `:= by` is how the thing is JUSTIFIED, not what it is -- except for
        # `set`, where the defining expression is the whole point of the clause.
        if re.match(r"set\s+\S+.*:=", line):
            take(line, i + 1)
            continue
        if re.match(r"(?:obtain|have|let)\s", line) and ":=" in line:
            take(line[:line.rindex(":=")], i + 1)
            continue
        if re.match(r"intro\s+\S+$", line):
            take(line, i + 1)
            continue

    # the theorem's own binders, plus every earlier step
    thm = re.search(r"^(theorem|lemma)\s+(\S+)(.*?):=\s*by\b", src, re.S | re.M)
    if thm:
        at = src.count("\n", 0, thm.start()) + 1
        for g in _split_groups(strip_comments(thm.group(3)))[0]:
            take(g, at)
    # Each earlier step, cited where its claim is WRITTEN but filed under its TACTIC's line: the
    # tactic line is the boundary `_introduced_by` cuts on, and a `pistis_segment` whose claim sits on
    # a later line than its keyword (the usual layout here) would otherwise fall inside the NEXT
    # sentence's window and be read as something that sentence introduces.
    for seg in parse_main(src):
        if seg["kind"] == "segment":
            take(f"{seg['name']} : {seg['claim']}", seg["line"], at=seg["line"])
    return out


def _introduced_by(ambient: list[dict], since: int, before: int) -> list[dict]:
    """The records a segment's own sentence brings into scope: those on lines in `(since, before)`.

    `since` is the previous `pistis_*` tactic's line, `before` is this one's, so the window is
    exactly the proof text that sits between the two sentences — the `obtain`/`set`/`have` the second
    one is formalized by. Order follows `ambient`, i.e. the proof's own order.

    This replaced a transitive closure over the names the claim mentions. See the module docstring:
    "what the claim needs in order to be read" has no floor, and the theorem's binders are the
    `statement` unit's business.
    """
    return [r for r in ambient if since < r["line"] < before]


def source_anchors(src: str) -> dict[str, list[int]]:
    """Where each unit is written in `Main.lean`, as UTF-16 `[start, end)` into the RAW source.

    The UI's left panel renders the whole file verbatim and makes exactly these regions clickable, so
    they have to be offsets into the real text, not into anything reformatted.

    A unit's region is its tactic invocation's HEAD — the keyword, the loc, and the NL string literal
    (`pistis_segment "1.3" "and \\[…\\]"`), which is contiguous in the source and is where `T_N` is
    read from. The claim after it is left alone.

    An `asm-*` unit's region is its whole `-- @pistis_assumption ("clause", TYPE)` marker, on the
    same principle: that marker is where BOTH of its targets are written, the clause being `T_N` and
    the type `T_F`. A marker is a comment, so this has to run on the RAW source — `_code_lines`
    blanks it, which is why `C_F` can never see one and why these are units rather than context.
    """
    def u16(i: int) -> int:
        return _utf16_len(src[:i])

    heads: dict[str, list[int]] = {}
    for m in _TACTIC_RE.finditer(src):
        q = src.index('"', m.end())                 # the loc literal
        loc, after_loc = read_string_literal(src, q)
        q2 = src.index('"', after_loc)              # the NL text literal
        _, after_text = read_string_literal(src, q2)
        kind = m.group(1)
        if kind == "intro":
            heads["statement"] = [u16(m.start()), u16(after_text)]
        elif kind == "segment":
            heads[f"seg-{loc}"] = [u16(m.start()), u16(after_text)]
        # pistis_wts / pistis_conclude carry NL but assert nothing, so they have no datapoint to open.
    for uid, a in assumption_markers(src).items():
        heads[uid] = [u16(a["start"]), u16(a["end"])]
    return heads


def assumption_markers(src: str) -> dict[str, dict]:
    """`{asm-<loc>-<k>: marker}` for every `@pistis_assumption` in `Main.lean`, in source order.

    A marker belongs to the first `pistis_*` tactic DECLARED BELOW IT — where `scaffold_main.py`
    emits it, and the same attribution `check_main.py` check 6 uses to hold the markers to
    `split.json`. `k` numbers them within their segment, in source order, so the ids line up with
    that segment's `assumptions` list index for index.

    A marker with an EMPTY text is skipped: `pistis_assumption ""` is the documented form for an
    input the prose does not state, so there is no NL clause to make a target out of and no unit to
    open. It still has a type, and the fill stage still has to discharge it; it simply is not an
    alignment, because alignment needs two sides.
    """
    locs: list[tuple[int, str]] = []
    for pos in (m.start() for m in _TACTIC_RE.finditer(src)):
        q = src.index('"', pos)
        loc, _ = read_string_literal(src, q)
        locs.append((pos, loc))

    out: dict[str, dict] = {}
    seen: dict[str, int] = {}
    for a in parse_assumptions(src):
        if not a["text"]:
            continue
        owner = next((loc for pos, loc in locs if pos > a["start"]), None)
        if owner is None:
            continue                                # an orphan below every tactic; check 6 reports it
        k = seen.get(owner, 0)
        seen[owner] = k + 1
        out[f"asm-{owner}-{k}"] = a
    return out


def segment_target(seg: dict) -> str:
    """A segment's formal target: the proposition inside `(stepK : …)`, and nothing else.

    `parse_main` already collapses the claim's whitespace, which is the only liberty taken with it —
    a claim written across three source lines becomes one. Everything else is the type as written.
    Single source of this rule: `check_targets.py` gates stored targets against it.
    """
    return seg["claim"]


def segment_nl_target(seg_text: str, assumptions: list[str]) -> str:
    r"""A segment's NL target: the segment MINUS its assumptions, a `GAP` left where each one was.

    This is the paper's `assert(s_i)` — what the sentence puts forward itself, once the substrings
    `split.json` lists under `assumptions` are taken out. It is what the claim is judged against, so
    it is what `T_N` holds; see the module docstring for why the whole sentence was wrong.

    Assumptions are located IN ORDER and non-overlapping, each searched for after the end of the
    previous one, which is the same reading `check_split.py` gates them under (every entry is a
    substring of its segment, listed in the order it is said). An entry that cannot be found that way
    is an error here and not a thing to paper over: it means the marker and the prose have parted
    company, and a target computed from a mis-located substring would cut the sentence in the wrong
    place. A segment with no assumptions comes back unchanged, which is eight of item1's nine.

    >>> segment_nl_target("since P and Q, therefore R", ["P", "Q"])
    'since … and …, therefore R'
    """
    out, at = [], 0
    for a in assumptions:
        if not a:                                   # an unattributed input ("" marker) quotes nothing
            continue
        i = seg_text.find(a, at)
        if i < 0:
            raise ValueError(f"assumption {a!r} is not a substring of the segment after offset "
                             f"{at} — split.json and the segment text disagree:\n{seg_text!r}")
        out.append(seg_text[at:i])
        out.append(GAP)
        at = i + len(a)
    out.append(seg_text[at:])
    return "".join(out)


def _statement_target(src: str) -> str:
    """T_F for the `statement` unit: the item's header + theorem signature, body replaced by `sorry`."""
    thm = re.search(r"^(theorem|lemma)\s", src, re.M)
    if not thm:
        raise ValueError("no `theorem`/`lemma` declaration in Main.lean")
    body = re.search(r":=\s*by\b", src[thm.start():])
    if not body:
        raise ValueError("no `:= by` after the theorem signature in Main.lean")
    head = "".join(ln + "\n" for ln in src[:thm.start()].splitlines()
                   if not _SCAFFOLD_LINE.match(ln))
    return normalize_tf(head + src[thm.start():thm.start() + body.end()] + " sorry")



def read_nl(item_dir, name: str) -> str:
    """One of the item's NL source files, verbatim: `name` is "nl_statement" or "nl_proof".

    The file's bytes ARE the paper's bytes — no JSON escaping, no trailing newline — so `newline=""`
    keeps universal-newline translation out of a value that is compared byte-for-byte downstream.
    """
    return (Path(item_dir) / "data" / f"{name}.txt").read_text(encoding="utf-8", newline="")


def proof_outline(item_dir) -> dict:
    """The item's align-then-label units, in proof order. See the module docstring."""
    item_dir = Path(item_dir)
    src = (item_dir / "Main.lean").read_text(encoding="utf-8")
    split = json.loads((item_dir / "split.json").read_text(encoding="utf-8"))
    meta = json.loads((item_dir / "meta.json").read_text(encoding="utf-8"))
    rel_main = f"items/item{meta['index']}/Main.lean"

    ambient = _ambient(src, rel_main)
    segs = parse_main(src)
    src_lines = src.splitlines()
    heads = source_anchors(src)

    def depth_of(line: int) -> int:
        """Nesting depth from the tactic's own indentation (2 spaces = the proof's top level)."""
        text = src_lines[line - 1] if 0 < line <= len(src_lines) else ""
        return max(0, (len(text) - len(text.lstrip())) - 2) // 2

    # the `pistis_*` line each segment's object introductions are measured back to
    tactic_lines = [0] + [s["line"] for s in segs]

    units: list[dict] = [{
        "id": "statement",
        "kind": "statement",
        "loc": segs[0]["loc"] if segs else "",
        "title": meta.get("result", meta.get("name", "")),
        "depth": 0,
        "nl_text": read_nl(item_dir, "nl_statement"),
        "nl_focus": "",
        "formal": _statement_target(src),
        "context": [],                      # the statement's T_F already carries its own context
        "coverage": "complete",
        "frame": None,
        "anchor": heads.get("statement"),
    }]

    markers = assumption_markers(src)

    for seg in segs:
        if seg["kind"] != "segment":
            continue                        # pistis_intro is the statement unit; wts/conclude carry no claim
        pos = int(seg["loc"].rsplit(".", 1)[-1])
        entry = split[pos] if 0 <= pos < len(split) else {}
        claim = segment_target(seg)
        assumps = list(entry.get("assumptions") or [])

        # The assumptions come FIRST, both on disk and in the panel, because that is where they are
        # written: the markers sit above the tactic. Each is its own (clause, TYPE) pair — the paper's
        # Atomic Faithfulness — and `check_main.py` check 6 is what guarantees the marker for
        # `assumps[k]` is the one this names `asm-<loc>-<k>`.
        for k, text in enumerate(assumps):
            uid = f"asm-{seg['loc']}-{k}"
            mark = markers.get(uid)
            if mark is None or mark["text"] != text:
                raise ValueError(
                    f"{uid}: split.json's assumption {text!r} has no matching "
                    f"`-- @pistis_assumption` marker on segment {seg['loc']} in Main.lean "
                    f"(got {mark and mark['text']!r}). Run `check_main.py` — this is ATOMICITY: the "
                    f"premise's formalization lives on that marker and nowhere else.")
            units.append({
                "id": uid,
                "kind": "assumption",
                "loc": seg["loc"],
                "title": f"{seg['name']} ← assumption {k + 1}",
                "depth": depth_of(seg["line"]),
                "nl_text": text,
                "nl_focus": text,           # the clause IS the target; seed one region over all of it
                "formal": mark["type"],
                "context": [],              # a marker consumes; it introduces nothing to be context
                "coverage": "complete",
                "frame": None,
                "anchor": heads.get(uid),
            })

        # What this sentence introduces — the `obtain`/`set`/`have` it is formalized by, and nothing
        # the theorem merely has in scope. Context, not target (see the module docstring).
        prev = max(ln for ln in tactic_lines if ln < seg["line"])
        units.append({
            "id": f"seg-{seg['loc']}",
            "kind": "segment",
            "loc": seg["loc"],
            "title": seg["name"],
            "depth": depth_of(seg["line"]),
            # the segment MINUS its assumptions: the claim answers the `assert`, not the premises
            "nl_text": segment_nl_target(seg["text"], assumps),
            "nl_focus": entry.get("assert", ""),
            "formal": claim,
            "context": _introduced_by(ambient, prev, seg["line"]),
            "coverage": "complete",
            "frame": entry.get("frame"),
            "anchor": heads.get(f"seg-{seg['loc']}"),
        })

    return {
        "index": meta["index"],
        "name": meta.get("name", ""),
        "result": meta.get("result", ""),
        "paper": meta.get("paper", ""),
        # `Main.lean` verbatim: the UI's left panel renders the whole file, and every unit's `anchor`
        # is a UTF-16 offset into exactly this string.
        "main": rel_main,
        "source": src,
        "units": units,
    }


def main(argv=None) -> int:
    import argparse
    ap = argparse.ArgumentParser(description="Print an item's align-then-label units.")
    ap.add_argument("item", help="path to an item dir, e.g. items/item1")
    args = ap.parse_args(argv)
    out = proof_outline(args.item)
    print(f"item{out['index']} — {out['result']}  ({len(out['units'])} units)")
    for u in out["units"]:
        pad = "  " * u["depth"]
        print(f"\n{pad}[{u['id']}] {u['kind']}  coverage={u['coverage']}")
        print(f"{pad}  T_N: {u['nl_text'][:90]!r}")
        print(f"{pad}  focus: {u['nl_focus']!r}")
        print(f"{pad}  T_F: {u['formal'][:120]!r}")
        for c in u["context"]:
            print(f"{pad}  C_F: {c['source'].split(':', 1)[1]:>6}  {c['signature'][:90]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
