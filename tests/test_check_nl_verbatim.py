r"""Tests for scripts/check_nl_verbatim.py — the repo-wide "no escaped NL" gate.

The regression this guards is specific: the NL was stored escaped in `Main.lean`, `split.json` and
several Python generators, and because escaping preserves the decoded VALUE, every gate in the repo
reported success. The only symptom was that Ctrl-F for a sentence of the paper found nothing. So the
first test here is the live repo itself, which is the only form this check has that cannot drift.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))

from check_nl_verbatim import MIN_LINE, check, escaped_lines, needles  # noqa: E402

PAPER = r"$T\subseteq I\times J$ means a real matrix whose entries outside $T$ are"
ESCAPED = PAPER.replace("\\", "\\\\")


def test_the_repo_has_no_escaped_nl():
    n_bad, msgs = check()
    assert n_bad == 0, "\n".join(msgs)


def test_the_repo_has_nl_lines_to_check():
    """Guards the gate against passing vacuously — an empty needle list would also report 0 bad."""
    pairs = needles()
    assert len(pairs) > 100
    assert all("\\" in line and len(line) >= MIN_LINE for line, _ in pairs)


def test_escaped_without_verbatim_is_a_hit():
    assert escaped_lines(f'  "{ESCAPED}"\n', [PAPER]) == [PAPER]


def test_raw_literal_is_not_a_hit():
    assert escaped_lines(f'  r"{PAPER}"\n', [PAPER]) == []


def test_escaped_alongside_verbatim_is_not_a_hit():
    """A file may SHOW the escaped form while also holding the real one — this docstring does."""
    assert escaped_lines(f"wrong: {ESCAPED}\nright: {PAPER}\n", [PAPER]) == []


def test_unrelated_text_is_not_a_hit():
    assert escaped_lines(r'a docstring about escaping: \\in and \\\\in', [PAPER]) == []
