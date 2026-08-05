"""Tests for scripts/check_split.py — the verbatim-tiling coverage gate.

Run:  python3 -m pytest tests/            (from repo root)
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))

from check_split import check_tiling  # noqa: E402


def seg(role, text, **extra):
    return {"role": role, "text": text, **extra}


# --------------------------------------------------------------------------- PASS cases

def test_simple_pass():
    stmt = "Prove that $1+1=2$."
    proof = "By definition, $1+1=2$."
    segs = [
        seg("intro", stmt),
        seg("deduction", "By definition, $1+1=2$."),
    ]
    ok, lines = check_tiling(segs, stmt, proof)
    assert ok, lines


def test_multi_segment_pass():
    stmt = "Prove $P$."
    # proof = three segments joined by single spaces
    proof = "First A. Then B. Thus $P$."
    segs = [
        seg("intro", stmt),
        seg("assume", "First A."),
        seg("deduction", "Then B."),
        seg("conclusion", "Thus $P$."),
    ]
    ok, lines = check_tiling(segs, stmt, proof)
    assert ok, lines


def test_internal_whitespace_preserved():
    # A double space and a newline INSIDE a single slice must be copied verbatim.
    stmt = "Statement."
    proof = "Line one\nwith a  double space."
    segs = [
        seg("intro", stmt),
        seg("deduction", "Line one\nwith a  double space."),
    ]
    ok, lines = check_tiling(segs, stmt, proof)
    assert ok, lines


def test_boundary_extra_space_carried_in_left_slice():
    # Source has TWO spaces between the two proof sentences. The single join-space covers one; the
    # extra one must live as a trailing space on the left slice.
    stmt = "S."
    proof = "A.  B."  # two spaces between A. and B.
    segs = [
        seg("intro", stmt),
        seg("deduction", "A. "),   # trailing space carries the extra
        seg("deduction", "B."),
    ]
    ok, lines = check_tiling(segs, stmt, proof)
    assert ok, lines


def test_boundary_newline_carried_in():
    # Display-math style: a newline at the boundary carried as leading part of the right slice.
    stmt = "S."
    proof = "Then\n$$x=1$$"
    segs = [
        seg("intro", stmt),
        seg("deduction", "Then"),
        seg("deduction", "\n$$x=1$$"),  # leading newline; join adds one space -> "Then \n$$x=1$$"? no
    ]
    # NOTE: join is "Then" + " " + "\n$$x=1$$" = "Then \n$$x=1$$" which is NOT "Then\n$$x=1$$".
    # So this SHOULD fail — the newline cannot also absorb the mandatory join-space. Verify it fails.
    ok, _ = check_tiling(segs, stmt, proof)
    assert not ok


def test_boundary_single_newline_as_the_join():
    # When the ONLY whitespace between two sentences is a single newline, the join inserts a space,
    # not a newline -> mismatch. The correct split keeps the newline inside a slice and there is no
    # extra token boundary. Demonstrate the correct verbatim handling: one slice spanning the newline.
    stmt = "S."
    proof = "Then\n$$x=1$$"
    segs = [
        seg("intro", stmt),
        seg("deduction", "Then\n$$x=1$$"),  # single slice, newline preserved
    ]
    ok, lines = check_tiling(segs, stmt, proof)
    assert ok, lines


# --------------------------------------------------------------------------- FAIL cases

def test_word_divergence_detected():
    stmt = "S."
    proof = "The cat sat."
    segs = [
        seg("intro", stmt),
        seg("deduction", "The dog sat."),  # cat -> dog
    ]
    ok, lines = check_tiling(segs, stmt, proof)
    assert not ok
    joined = "\n".join(lines)
    assert "diverges at word" in joined
    assert "'cat'" in joined and "'dog'" in joined


def test_missing_tail_detected():
    stmt = "S."
    proof = "A B C D E."
    segs = [
        seg("intro", stmt),
        seg("deduction", "A B C"),  # dropped "D E."
    ]
    ok, lines = check_tiling(segs, stmt, proof)
    assert not ok
    assert any("continues past" in l for l in lines)


def test_overrun_detected():
    stmt = "S."
    proof = "A B."
    segs = [
        seg("intro", stmt),
        seg("deduction", "A B. Extra words."),  # too much
    ]
    ok, lines = check_tiling(segs, stmt, proof)
    assert not ok
    assert any("runs past the end" in l for l in lines)


def test_whitespace_only_mismatch_detected():
    stmt = "S."
    proof = "A.  B."  # two spaces in source
    segs = [
        seg("intro", stmt),
        seg("deduction", "A."),   # no trailing space -> join gives single space only
        seg("deduction", "B."),
    ]
    ok, lines = check_tiling(segs, stmt, proof)
    assert not ok
    assert any("whitespace mismatch" in l for l in lines)


def test_intro_must_match_statement():
    stmt = "The real statement."
    proof = "The proof."
    segs = [
        seg("intro", "A different statement."),  # intro != nl_statement
        seg("deduction", "The proof."),
    ]
    ok, lines = check_tiling(segs, stmt, proof)
    assert not ok
    assert any("statement/intro" in l for l in lines)


def test_empty_split_fails():
    ok, lines = check_tiling([], "S.", "P.")
    assert not ok
    assert any("empty" in l for l in lines)


def test_first_segment_must_be_intro():
    stmt = "S."
    proof = "P."
    segs = [seg("deduction", "S."), seg("deduction", "P.")]
    ok, lines = check_tiling(segs, stmt, proof)
    assert not ok
    assert any("role 'intro'" in l for l in lines)


def test_only_one_intro_allowed():
    stmt = "S."
    proof = "P."
    segs = [seg("intro", "S."), seg("intro", "P.")]
    ok, lines = check_tiling(segs, stmt, proof)
    assert not ok
    assert any("only segment 0 may be 'intro'" in l for l in lines)


# --------------------------------------------------------------------------- real-shaped case

def test_proofnet8_shaped():
    # Mirrors the REAL proofnet-8 structure: prose sentences separated by ". " (period-space), and a
    # display-math block ($$ ... $$) with its surrounding newlines living INSIDE a single segment.
    stmt = r"Prove that in the ring $\mathbb{Z}[x],(2) \cap(x)=(2 x)$."
    # Real text: "Let ...$. Then there exists ... such that\n$$\nf(x)=2 x g(x)\n$$\nBut this means ..."
    proof = (
        r"Let $f(x) \in(2 x)$. "
        r"Then there exists some polynomial $g(x) \in \mathbb{Z}$ such that"
        "\n$$\nf(x)=2 x g(x)\n$$\n"
        r"But this means that $f(x) \in(2)$."
    )
    segs = [
        seg("intro", stmt),
        # single-space boundary "$. Then": the join provides the one space, so NO trailing space here
        seg("assume", r"Let $f(x) \in(2 x)$.", objects_introduced=[r"$f(x)$"]),
        # sentence 2 owns the display-math block + its newlines (internal + boundary), verbatim
        seg("deduction",
            r"Then there exists some polynomial $g(x) \in \mathbb{Z}$ such that"
            "\n$$\nf(x)=2 x g(x)\n$$\n"
            r"But this means that $f(x) \in(2)$."),
    ]
    ok, lines = check_tiling(segs, stmt, proof)
    assert ok, lines
