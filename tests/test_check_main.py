"""Tests for scripts/check_main.py and scripts/pistis_lean.py."""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))

from check_main import check_main  # noqa: E402
from pistis_lean import parse_main, parse_assumptions, read_string_literal  # noqa: E402

STMT = "Prove $P$."
PROOF = "Since $a=b$, we get $x=y$. Thus $P$."

HEADER = (
    "import Mathlib\nimport Pistis\nset_option linter.unusedTactic false\n\n"
    "theorem foo : True := by\n"
)


def _main(body: str) -> str:
    return HEADER + body


def _good_body(closer="  exact step2"):
    return (
        '  pistis_intro "1.0"\n    "Prove $P$."\n\n'
        '  -- @pistis_assumption ("$a=b$", a = b)\n'
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
    assert kinds == ["intro", "segment", "conclude"]
    seg = segs[1]
    assert seg["loc"] == "1.1" and seg["name"] == "step1" and seg["claim"] == "x = y"


def test_parse_assumptions():
    a = parse_assumptions(_main(_good_body()))
    assert len(a) == 1 and a[0]["text"] == "$a=b$" and a[0]["type"] == "a = b"


# --------------------------------------------------------------------------- PASS

def test_mapped_passes():
    # note the proof tiling: "Since $a=b$, we get $x=y$." + " " + "Thus $P$."
    ok, lines = check_main(_main(_good_body()), STMT, PROOF)
    assert ok, lines


# --------------------------------------------------------------------------- FAIL cases

def test_true_claim_fails():
    body = _good_body().replace("(step1 : x = y)", "(step1 : True)")
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


def test_todo_assumption_fails():
    body = _good_body().replace('("$a=b$", a = b)', '("$a=b$", TODO)')
    ok, lines = check_main(_main(body), STMT, PROOF)
    assert not ok
    assert any("TODO" in l for l in lines)


def test_edited_text_breaks_tiling():
    body = _good_body().replace("we get $x=y$", "we obtain $x=y$")  # tampered text
    ok, lines = check_main(_main(body), STMT, PROOF)
    assert not ok
    assert any("diverges" in l for l in lines)
