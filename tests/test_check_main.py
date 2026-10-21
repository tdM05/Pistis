"""Tests for scripts/check_main.py and scripts/pistis_lean.py."""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))

from check_main import check_main  # noqa: E402
from pistis_lean import parse_main, read_string_literal  # noqa: E402
from scaffold_main import _lean_str  # noqa: E402

STMT = "Prove $P$."
PROOF = "Since $a=b$, we get $x=y$. Thus $P$."

# NL with real LaTeX backslashes. The plain STMT/PROOF above have none, so they satisfy the
# verbatim-bytes gate no matter how they are stored — which is why the escaped-NL defect lived here
# undetected. Anything about storage has to be tested on text that actually contains a backslash.
STMT_TEX = r"Let $T\subseteq I\times J$ be finite."
SEG_TEX = r"Since $x\in\ker D$, we have $x_jy_s=0$."
CONC_TEX = r"Thus $\tau\ne0$."
PROOF_TEX = SEG_TEX + " " + CONC_TEX

HEADER = (
    "import Mathlib\nimport Pistis\nset_option linter.unusedTactic false\n\n"
    "theorem foo : True := by\n"
)


def _main(body: str) -> str:
    return HEADER + body


def _good_body(closer="  exact step2"):
    return (
        '  pistis_intro "1.0"\n    "Prove $P$."\n\n'
        '  pistis_assumption "1.1" "$a=b$" (asm0 : a = b) := by sorry\n'
        '  pistis_segment "1.1"\n    "Since $a=b$, we get $x=y$."\n    (step1 : x = y) := by sorry\n\n'
        '  pistis_conclude "1.2"\n    "Thus $P$."\n\n'
        f"{closer}\n"
    )


# --------------------------------------------------------------------------- parser

def test_read_string_literal_decodes_escapes():
    txt, end = read_string_literal(r'"a\\b\"c"', 0)
    assert txt == r'a\b"c'


def test_parse_main_recovers_segments():
    segs = parse_main(_main(_good_body()))
    kinds = [s["kind"] for s in segs]
    assert kinds == ["intro", "assumption", "segment", "conclude"]
    seg = segs[2]
    assert seg["loc"] == "1.1" and seg["name"] == "step1" and seg["claim"] == "x = y"


def test_parse_main_recovers_assumption():
    """A `pistis_assumption` is parsed exactly like a `pistis_segment` — same tail shape — except its
    `loc` is the loc of the segment it is wired to, not a loc of its own."""
    asm = parse_main(_main(_good_body()))[1]
    assert asm["kind"] == "assumption"
    assert asm["loc"] == "1.1"              # the loc of the pistis_segment it is wired to
    assert asm["name"] == "asm0" and asm["claim"] == "a = b" and asm["text"] == "$a=b$"


# --------------------------------------------------------------------------- PASS

def test_mapped_passes():
    # note the proof tiling: "Since $a=b$, we get $x=y$." + " " + "Thus $P$."
    # (the pistis_assumption's own text is NOT tiled — it is a substring of the segment's text,
    # already counted there)
    ok, lines = check_main(_main(_good_body()), STMT, PROOF)
    assert ok, lines


# --------------------------------------------------------------------------- FAIL cases

def test_true_claim_fails():
    body = _good_body().replace("(step1 : x = y)", "(step1 : True)")
    ok, lines = check_main(_main(body), STMT, PROOF)
    assert not ok
    assert any("vacuous" in l for l in lines)


def test_true_assumption_fails():
    """`True` is the scaffold's unfilled-placeholder sentinel for an assumption's type too — the map
    agent must replace it with the real type, just like a segment's claim."""
    body = _good_body().replace("(asm0 : a = b)", "(asm0 : True)")
    ok, lines = check_main(_main(body), STMT, PROOF)
    assert not ok
    assert any("vacuous" in l for l in lines)


def test_stray_sorry_fails():
    ok, lines = check_main(_main(_good_body(closer="  sorry -- @pistis_closer: replace me")), STMT, PROOF)
    assert not ok
    assert any("stray sorry" in l for l in lines)


def test_body_sorry_is_allowed():
    # a `have … := by sorry` in the closer region is a legal body-sorry, not stray
    closer = "  have hbridge : x = y := by sorry\n  exact step2"
    ok, lines = check_main(_main(_good_body(closer=closer)), STMT, PROOF)
    assert ok, lines


def test_edited_text_breaks_tiling():
    body = _good_body().replace("we get $x=y$", "we obtain $x=y$")  # tampered text
    ok, lines = check_main(_main(body), STMT, PROOF)
    assert not ok
    assert any("diverges" in l for l in lines)


# --------------------------------------------------------------------------- verbatim bytes
#
# The NL in a Main.lean must be stored in a RAW literal, so the file's bytes are the paper's bytes
# and `grep`/Ctrl-F for a sentence of the proof finds it. An ordinary escaped literal has the right
# VALUE, so it satisfies every other check here; only the byte check sees the difference.

def _tex_body(raw: bool) -> str:
    def lit(s: str) -> str:
        return f'r"{s}"' if raw else '"' + s.replace("\\", "\\\\") + '"'
    return (
        f'  pistis_intro "1.0"\n    {lit(STMT_TEX)}\n\n'
        f'  pistis_segment "1.1"\n    {lit(SEG_TEX)}\n    (step1 : x = y) := by sorry\n\n'
        f'  pistis_conclude "1.2"\n    {lit(CONC_TEX)}\n\n'
        "  exact step1\n"
    )


def test_raw_literal_parses_to_the_same_text():
    raw, esc = parse_main(_main(_tex_body(True))), parse_main(_main(_tex_body(False)))
    assert [s["text"] for s in raw] == [STMT_TEX, SEG_TEX, CONC_TEX]
    assert [s["text"] for s in raw] == [s["text"] for s in esc]  # same value, different bytes


def test_raw_nl_passes():
    src = _main(_tex_body(True))
    ok, lines = check_main(src, STMT_TEX, PROOF_TEX)
    assert ok, lines
    assert STMT_TEX in src and SEG_TEX in src  # the point: the bytes are in the file


def test_escaped_nl_fails_the_byte_gate_while_coverage_passes():
    """The exact defect: decoded values tile the source perfectly, but the file's bytes are escaped.

    Asserting that coverage PASSES here is the part that matters — it pins down that the older checks
    cannot see this, so the byte check is doing work nothing else does.
    """
    src = _main(_tex_body(False))
    assert STMT_TEX not in src                       # the paper's bytes are NOT in the file
    ok, lines = check_main(src, STMT_TEX, PROOF_TEX)
    assert not ok
    assert any("reproduces source exactly" in l for l in lines)   # coverage is happy
    assert any("not verbatim" in l for l in lines)                # the byte gate is not


def test_raw_literal_hides_sorry_and_trailing_backslash_from_the_code_scan():
    """A raw literal must be skipped as a unit by the stray-`sorry` scan.

    Two traps: the word `sorry` inside NL prose is not a tactic, and a backslash immediately before
    the closing quote (`r"…\\"`) does not escape it — reading a raw literal with ordinary-string rules
    runs past the end and blanks real code after it.
    """
    nl = r"We are sorry, but $A\subseteq B\$"
    body = (
        f'  pistis_intro "1.0"\n    {_lean_str(nl)}\n\n'
        '  exact trivial\n'
    )
    segs = parse_main(_main(body))
    assert [s["text"] for s in segs] == [nl]
    # The overall verdict is beside the point (there is no proof to tile); only the scan matters.
    lines = check_main(_main(body), nl, "")[1]
    assert not any("stray sorry" in l for l in lines), lines


# --------------------------------------------------------------------------- assumptions wired
#
# ATOMICITY: a segment has a SINGLE assertion, its premises are `assumps`. `split.json` draws that
# line; `Main.lean` must keep it. The way to break it that NO check could see was to delete a
# `pistis_assumption` and fold its content into the claim as an extra conjunct — the vacuous-claim
# check only rejects an assumption left as `True`, and a deleted one leaves nothing to reject.

SPLIT = [
    {"role": "intro", "text": "Prove $P$."},
    {"text": "Since $a=b$, we get $x=y$.", "assumptions": ["$a=b$"], "assert": "we get $x=y$"},
    {"role": "conclusion", "text": "Thus $P$."},
]

ASM0 = '  pistis_assumption "1.1" "$a=b$" (asm0 : a = b) := by sorry\n'


def test_assumptions_wired_passes():
    ok, lines = check_main(_main(_good_body()), STMT, PROOF, SPLIT)
    assert ok, lines
    assert any("assumptions wired: 1" in l for l in lines)


def test_deleted_assumption_fails_while_every_other_check_passes():
    """The regression this check exists for, in the shape it actually occurred.

    `oai_math/items/item1` segment 1.7 dropped both assumptions and made the two premises conjuncts
    of the claim. Asserting that coverage still PASSES is the load-bearing part: it pins down that
    the other checks cannot see this, so the assumptions-wired check is doing work nothing else does.
    """
    body = _good_body().replace(ASM0, "")
    body = body.replace("(step1 : x = y)", "(step1 : a = b ∧ x = y)")
    assert "pistis_assumption" not in body

    ok, lines = check_main(_main(body), STMT, PROOF, SPLIT)
    assert not ok
    assert any("reproduces source exactly" in l for l in lines)        # coverage is happy
    assert not any("vacuous" in l or "not verbatim" in l or "stray" in l
                   for l in lines)                                     # so is everything else
    assert any("MISSING" in l and "$a=b$" in l for l in lines)

    # and with no split.json supplied, nothing catches it — which was the state of the repo
    assert check_main(_main(body), STMT, PROOF)[0]


def test_extra_assumption_fails():
    body = _good_body().replace(
        ASM0, ASM0 + '  pistis_assumption "1.1" "we get $x=y$" (asm1 : x = y) := by sorry\n')
    ok, lines = check_main(_main(body), STMT, PROOF, SPLIT)
    assert not ok
    assert any("EXTRA" in l and "we get $x=y$" in l for l in lines)


def test_unattributed_empty_assumption_is_allowed():
    """`pistis_assumption "<loc>" ""` is the documented form for an input the prose does not state, so
    `split.json` has no entry to match it against and it is not an extra."""
    body = _good_body().replace(
        ASM0, ASM0 + '  pistis_assumption "1.1" "" (asm1 : Nontrivial G) := by sorry\n')
    ok, lines = check_main(_main(body), STMT, PROOF, SPLIT)
    assert ok, lines
    assert any('1 unattributed ("")' in l for l in lines)


def test_assumption_order_must_match_split():
    split = [dict(SPLIT[0]),
             {**SPLIT[1], "assumptions": ["Since $a=b$", "we get $x=y$"]},
             dict(SPLIT[2])]
    body = _good_body().replace(
        ASM0,
        '  pistis_assumption "1.1" "we get $x=y$" (asm0 : x = y) := by sorry\n'
        '  pistis_assumption "1.1" "Since $a=b$" (asm1 : a = b) := by sorry\n')
    ok, lines = check_main(_main(body), STMT, PROOF, split)
    assert not ok
    assert any("wrong order" in l for l in lines)


def test_orphan_assumption_loc_is_reported():
    """An assumption wired to a `loc` no `pistis_segment` (or structural tactic) carries is an orphan
    — the analogue of the old "sits below every pistis_* tactic" case, now driven by `loc` equality
    rather than source position."""
    body = _good_body().replace(ASM0, '  pistis_assumption "9.9" "$a=b$" (asm9 : a = b) := by sorry\n')
    ok, lines = check_main(_main(body), STMT, PROOF, SPLIT)
    assert not ok
    assert any("no matching pistis_segment" in l for l in lines)


def test_lean_str_round_trips_and_keeps_text_verbatim():
    for s in (STMT_TEX,
              r"a\b",
              'has a " quote',
              'has "# both',
              r"ends with a backslash \ ",
              "two\nlines\n\nand a blank"):
        lit = _lean_str(s)
        back, end = read_string_literal(lit, 0)
        assert back == s, (s, lit, back)
        assert end == len(lit), (s, lit)
        assert s in lit, (s, lit)                    # verbatim: the literal contains the text itself
