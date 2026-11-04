#!/usr/bin/env python3
r"""`item1_gt`'s K-Pistis annotation — the GT proof (`items/item1/_gt/MaxSupportKernel.lean`,
flattened into `kpistis/items/item1_gt/Proof.lean`) aligned against the SAME NL target as
`item1`'s own annotation.

The point of this file is not a second independent annotation; it is a diff instrument. Both trees
share `T_N` byte for byte (`item1_gt`'s NL data is a copy of `item1`'s), so every NL region here is
named with the exact same needle `item1`'s `annotate_item1.py` used, and `C_N` is lifted from there
unchanged — only the FORMAL side and the EDGES differ, because only the formal side differs between
the two Lean files. Where `item1/root`'s edge for a step is `v=1` with "refined below" and this
file's edge for the same step is `v=0`, that is a located, checked instance of unfaithfulness in the
GT proof, not a prose claim about it (see `items/item1/ai.md` for the prose version).

Depth 2 only (`root`), on purpose — the question this file answers is "does each proof step's
*statement* still say what the sentence says", which the root's own edges already settle. Going a
level deeper (as `item1/root/1.2/formula` does) would be re-running the first prototype's exercise;
nothing here needs it.

    python3 kpistis/annotate_item1_gt.py            # write
    python3 kpistis/annotate_item1_gt.py --check    # validate without writing
"""
from __future__ import annotations

import argparse
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import model
from model import BOT
from annotate_item1 import DEFN, MAXRANK, CONCL, INDICES, DEF_DTAU, SUPPOSE, Unit as _Unit

ITEM = "item1_gt"


class Unit(_Unit):
    """`annotate_item1.Unit`, pointed at `item1_gt` instead of `item1`.

    Only `__init__`'s `model.load` call and `c`'s `paper()` lookup need to know the item name;
    everything else — region naming by needle, edge linking, `build()`'s re-anchoring — is identical,
    so it is inherited rather than copied.
    """

    def __init__(self, path: str, **meta):
        self.path = path
        self.base = model.load(ITEM, path)
        self.meta = meta
        self.F, self.N, self.C, self.edges = {}, {}, {}, []

    def c(self, region: str, *needles, why: str, nth=None):
        text = model.load(ITEM, "root")["T_N"]          # same paper, loaded from THIS item's root
        self.C.setdefault(region, []).append(
            {"spans": [model.find_span(text, n, occurrence=k)
                       for n, k in zip(needles, nth or [0] * len(needles))],
             "why": " ".join(why.split())})
        return self


def root() -> Unit:
    u = Unit("root", title="Lemma 3.2 (Kernels at maximum support rank) — GT",
             category="document", child_category="proof step", done=True)
    var = "variable {I J : Type*} [Fintype I] [Fintype J]"

    # ---- F regions. `idx`'s `variable` line is shared with `def` and `thm` for the same reason it
    # is in `item1/root`: the paper states finiteness twice, so Lean's one `variable` line has to sit
    # in both regions that answer those two sentences (README, *No formal context*).
    u.f("hdr", "import Mathlib\nopen Matrix\nset_option linter.unusedVariables false")
    u.f("def", var,
        "def SupportedOn (T : Set (I × J)) (D : Matrix I J ℝ) : Prop :=\n"
        "  ∀ s j, (s, j) ∉ T → D s j = 0")
    u.f("thm", var,
        "theorem kernel_support {T : Set (I × J)} {D : Matrix I J ℝ}\n"
        "    (hD : SupportedOn T D)\n"
        "    (hmax : ∀ A : Matrix I J ℝ, SupportedOn T A → A.rank ≤ D.rank)\n"
        "    {x : J → ℝ} {y : I → ℝ}\n"
        "    (hx : x ∈ LinearMap.ker D.mulVecLin)\n"
        "    (hy : y ∈ LinearMap.ker Dᵀ.mulVecLin)\n"
        "    {s : I} {j : J} (hsj : (s, j) ∈ T) :\n"
        "    x j * y s = 0 := by")
    u.f("tech", "classical")
    u.f("contra", "by_contra hxy")
    u.f("early-hxj", "have hxj : x j ≠ 0 := by sorry")
    u.f("early-hys", "have hys : y s ≠ 0 := by sorry")
    u.f("supported", "have hsupport : SupportedOn T (D + Matrix.single s j (1 : ℝ)) := by sorry")
    u.f("identity", "have hEx : (D + Matrix.single s j (1 : ℝ)).mulVec x\n"
                     "      = x j • (Pi.single s (1 : ℝ) : I → ℝ) := by sorry")
    u.f("mem", "have he : (Pi.single s (1 : ℝ) : I → ℝ) ∈\n"
               "      LinearMap.range (D + Matrix.single s j (1 : ℝ)).mulVecLin := by sorry")
    u.f("containment", "have hle : LinearMap.range D.mulVecLin ≤\n"
                        "      LinearMap.range (D + Matrix.single s j (1 : ℝ)).mulVecLin := by sorry")
    u.f("notmem", "have hnot : (Pi.single s (1 : ℝ) : I → ℝ) ∉ LinearMap.range D.mulVecLin := by sorry")
    u.f("rank", "have hlt : D.rank < (D + Matrix.single s j (1 : ℝ)).rank := by sorry")
    u.f("close", "exact (not_lt_of_ge (hmax _ hsupport)) hlt")

    # ---- N regions. Named with the SAME needles `item1/root` used, against the SAME `nl_statement +
    # nl_proof` text — this is what makes the two trees comparable edge for edge.
    u.n("defn", r"""For finite index sets $I,J$, a matrix supported on
$T\subseteq I\times J$ means a real matrix whose entries outside $T$ are
zero; entries in $T$ are allowed to vanish.""")
    u.n("thm", r"""\begin{lemma}[Kernels at maximum support rank]\label{lem:kernel-support}
Let $T\subseteq I\times J$, where $I$ and $J$ are finite.  Suppose that
$D:\R^J\to\R^I$ has maximum rank among all real matrices supported on $T$.
Then, for every $x\in\ker D$, every $y\in\ker D^{\mathsf T}$, and every
$(s,j)\in T$, one has $x_jy_s=0$.""")
    u.n("1.1", "Suppose instead that $x_jy_s\\ne0$.")
    u.n("1.2", r"""For a nonzero real $\tau$, the matrix
$D_\tau=D+\tau e_s e_j^{\mathsf T}$ is still supported on $T$,""")
    u.n("1.3", r"""and
\[
 D_\tau x=\tau x_j e_s.
\]""")
    u.n("1.4", "Thus $e_s\\in\\im D_\\tau$.")
    u.n("1.5", r"""Moreover, for every $w\in\R^J$,
\[
 Dw=D_\tau w-\tau w_j e_s\in\im D_\tau,
\]""")
    u.n("1.6", "so the entire old image $\\im D$ is contained in $\\im D_\\tau$.")
    u.n("1.7", "On the other hand, $y$ annihilates $\\im D$ and $y_s\\ne0$, so\n$e_s\\notin\\im D$.")
    u.n("1.8", "Therefore $\\rank D_\\tau>\\rank D$,")
    u.n("1.9", "a contradiction.")

    # ---- C_N, lifted from `item1/root` unchanged (same needles, same paper). This is not re-authored
    # judgment; `item1_gt` inherits it because the sentences need the same reading regardless of which
    # Lean file is being checked against them.
    u.c("defn", r"Let $T\subseteq I\times J$, where $I$ and $J$ are finite.", why="""
        The finiteness of $I$ and $J$ is asserted HERE as well, inside the lemma, and Lean asserts it
        once — `variable {I J : Type*} [Fintype I] [Fintype J]`. So the `variable` line is in this
        region and in `thm`, shared exactly as in `item1/root` (same paper, same double statement).""")
    u.c("thm", r"$\rank D_\tau>\rank D$", why=r"""
        'has maximum rank among all real matrices supported on $T$' is the hypothesis `hmax`, but the
        paper never defines `rank` and writes it for the first and only time in the proof's last
        line — a forward reference, same as in `item1`.""")
    u.c("thm", DEFN, why="""
        'supported on $T$' twice in one lemma, defined in the paragraph above.""")
    u.c("1.1", CONCL, why="""
        The conclusion this negates — without it 'instead' names nothing. Same back-reference as
        `item1/root/1.1`.""")
    u.c("1.1", "a contradiction.", why="""
        Where the reductio opened here is discharged, nine sentences later.""")
    u.c("1.2", DEFN, why="""
        'is still supported on $T$' needs the definition from thirteen lines earlier.""")
    u.c("1.2", MAXRANK, why=r"""
        What $D$ is — the maximum-rank matrix fixed by the lemma's hypothesis.""")
    u.c("1.2", INDICES, why=r"""
        Where $s$ and $j$ come from. $e_s$, $e_j^{\mathsf T}$ are never defined anywhere in the
        paper — the nearest it comes is this binder.""")
    u.c("1.3", DEF_DTAU, why=r"""
        What $D_\tau$ is, from the previous sentence; $D_\tau x=\tau x_j e_s$ is a computation from
        that definition.""")
    u.c("1.3", r"every $x\in\ker D$", why=r"""
        That $x\in\ker D$ is what makes the $D$ term of $D_\tau x$ vanish; the paper never shows the
        cancellation.""")
    u.c("1.4", r"""\[
 D_\tau x=\tau x_j e_s.
\]""", why=r"""
        The equation this concludes from, immediately above.""")
    u.c("1.4", SUPPOSE, why=r"""
        The step needs $x_j\ne0$ to divide by $\tau x_j$ — from the reductio supposition, not from
        anywhere near this sentence.""")
    u.c("1.5", DEF_DTAU, why=r"""What $D_\tau$ is; $Dw=D_\tau w-\tau w_j e_s$ is that rearranged.""")
    u.c("1.5", r"Thus $e_s\in\im D_\tau$.", why=r"""
        Why the right-hand side lies in $\im D_\tau$: by definition and by the previous sentence.""")
    u.c("1.6", r"""Moreover, for every $w\in\R^J$,
\[
 Dw=D_\tau w-\tau w_j e_s\in\im D_\tau,
\]""", why=r"""
        The 'so' makes this a conclusion of the previous sentence, which is where all the content
        is.""")
    u.c("1.7", r"every $y\in\ker D^{\mathsf T}$", why=r"""
        That $y\in\ker D^{\mathsf T}$ is why '$y$ annihilates $\im D$' is true — eleven lines up.""")
    u.c("1.7", SUPPOSE, why=r"""
        $y_s\ne0$ is asserted flatly here, but it follows from the reductio supposition, not from
        anything nearby.""")
    u.c("1.8", r"so the entire old image $\im D$ is contained in $\im D_\tau$.", why=r"""
        One half of 'Therefore': $\im D\subseteq\im D_\tau$.""")
    u.c("1.8", r"Thus $e_s\in\im D_\tau$.", r"$e_s\notin\im D$.", why="""
        The other half: strictness of the inclusion.""", nth=[0, 0])
    u.c("1.9", MAXRANK, why="""
        The maximality that is contradicted, fifteen lines up.""")
    u.c("1.9", "is still supported on $T$,", why=r"""
        Why `hmax` applies to $D_\tau$ at all — step 1.2.""")

    # ---- edges. The boilerplate ones are identical in kind to `item1/root`'s; everything from
    # `contra` on down is where this file earns its keep.
    u.link("hdr", BOT, 1, """
        `import Mathlib`, `open Matrix`, the linter `set_option` — how the file is built, nothing it
        asserts. Same ⊥ as `item1/root`.""")
    u.link("def", "defn", 1, """
        The paper's definition, matched exactly as in `item1/root` — GT's `SupportedOn` is the same
        `def`, byte for byte.""")
    u.link("thm", "thm", 1, r"""
        The lemma, binder for binder — GT's final `kernel_support` wrapper has the IDENTICAL
        signature to `item1`'s (it is the one place GT does not diverge from the official
        statement). 'where $I$ and $J$ are finite' is the shared `variable` line, exactly as in
        `item1/root`.""")
    u.link("tech", BOT, 1, """
        `classical`, for the same `DecidableEq` reason as `item1/root`.""")
    u.link("contra", "1.1", 1, """
        `by_contra hxy` opens the same reductio as 'Suppose instead that $x_jy_s\\ne0$' — this much
        is unchanged from the faithful version.""")
    u.link("early-hxj", BOT, 1, """
        `x j ≠ 0` is never asserted ANYWHERE in the paper — not in this sentence, not as one of 1.7's
        two declared assumptions, not at all (see `items/item1/ai.md`, finding 2). The ⊥ judgment
        itself is correct — there is truly no sentence to point at — but the reason it is correct is
        a genuine gap in the paper's own rigor: 1.4 needs this fact to divide by $\\tau x_j$ (with
        $\\tau=1$ here, by $x_j$), and nothing in the text ever supplies it. GT derives it by
        contrapositive on the reductio, immediately after opening it — which is ALSO where this
        region sits, before step 1.2 even starts.""")
    u.link("early-hys", "1.7", 0, """
        `y s ≠ 0` is split.json's own second assumption of segment 1.7 ('$y_s\\ne0$'), so this is NOT
        a ⊥ edge — there IS a sentence for it, 'On the other hand, ... $y_s\\ne0$, so $e_s\\notin\\im
        D$.' But GT proves `hys` immediately after `by_contra hxy`, lines before step 1.2 even
        starts, not at the sentence that states it. Faithful placement (`item1/root/1.7`, `hker`)
        proves all three of 1.7's clauses together, where the sentence is; GT proves this one clause
        five `have`s too early. Verdict 0: the FACT is right, the LOCATION is not — a crossing the
        edge itself should carry rather than hide.""")
    u.link("supported", "1.2", 0, r"""
        **The edge `item1_gt` exists to produce.** The sentence is universally quantified — 'For a
        nonzero real $\tau$, the matrix $D_\tau=D+\tau e_s e_j^{\mathsf T}$ is still supported on
        $T$' — but GT's term is `D + Matrix.single s j (1 : ℝ)`: no `τ`, no scalar multiple, the
        coefficient is the literal `1`. GT proves the $\tau=1$ instance and nothing more general;
        there is no bound variable in this `have` for 'for a nonzero real $\tau$' to quantify. (Where
        the faithful version keeps $\tau$ all the way through — `item1/root/1.2`'s `formula` child is
        built around exactly this term being `τ • Matrix.single s j 1` — this is the term it is NOT.)
        Verdict 0: the claim proved is strictly weaker than the sentence states.""")
    u.link("identity", "1.3", 0, r"""
        Same narrowing one step further in: the sentence displays $D_\tau x=\tau x_j e_s$, and `hEx`
        states `x j • (Pi.single s 1)` with no `τ` anywhere — the $\tau=1$ specialization inherited
        from `supported`, not a new choice made here, but the Lean term is still strictly narrower
        than the displayed identity. Verdict 0 for the same reason as `supported`.""")
    u.link("mem", "1.4", 1, """
        `he : e_s ∈ range (D + single s j 1).mulVecLin`, from `identity` by scaling — the one
        argument in this region (divide by a nonzero scalar, which needs `hxj`) is sound on its own
        terms. The $\\tau=1$ narrowing is `identity`'s and `supported`'s to answer for, not this
        region's; what THIS clause asserts about the perturbed matrix it is given, it asserts
        correctly.""")
    u.link(BOT, "1.5", 1, r"""
        No region of `Proof.lean` answers this sentence at all — not narrowed, not relocated, simply
        absent. GT's analogue of 'for every $w\in\R^J$, $Dw=D_\tau w-\tau w_j e_s\in\im D_\tau$' is
        the anonymous local fact `hEw` inside the real proof of `range_lt_range_add_single`'s strict
        inequality (`_gt/MaxSupportKernel.lean`) — used once, inline, never stated as a top-level
        `have`, and invisible here because every body is `sorry`. The ⊥ judgment is correct (there is
        genuinely nothing to point `S_F` at), which is why this is `v=1`; what it records is that the
        universally-quantified identity the paper displays as its own sentence never becomes a named
        fact in GT's proof at all, let alone a general one.""")
    u.link("containment", "1.6", 1, """
        `hle : range D.mulVecLin ≤ range (D + single s j 1).mulVecLin` is exactly 'the entire old
        image im D is contained in im Dτ' — the containment claim itself is right. (It is proved using
        the anonymous `hEw` that 1.5 has no name for, but that is 1.5's edge to answer for, not this
        one's.)""")
    u.link("notmem", "1.7", 0, """
        `hnot` states only the sentence's THIRD clause, 'so $e_s\\notin\\im D$'. The first clause,
        '$y$ annihilates $\\im D$', is never a named fact anywhere in GT — it is proved anonymously
        inside `hnot`'s own (here `sorry`-hidden) body via `dotProduct_transpose_mulVec` — and the
        second clause, '$y_s\\ne0$', was already proved five lines earlier (`early-hys`, which already
        carries its own verdict-0 edge to this same region). So the sentence's three clauses map to
        Lean three different ways: one entirely unnamed, one present but five lines too early, one
        present and in place. `item1/root/1.7`'s `hker` is the single conjunctive `have`, at this
        exact location, that GT's structure never assembles. Verdict 0.""")
    u.link("rank", "1.8", 1, r"""
        `hlt : D.rank < (D + single s j 1).rank` is 'Therefore $\rank D_\tau>\rank D$' — this step's
        own content is right; it inherits the $\tau=1$ narrowing from upstream rather than adding any.""")
    u.link("close", "1.9", 1, """
        `exact (not_lt_of_ge (hmax _ hsupport)) hlt` closes the reductio against `hmax`, exactly as
        the faithful version's final `exact absurd (hmax Dτ hsupp) (not_le.mpr hrank)` does.""")
    return u


UNITS = [root]


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Write item1_gt's K-Pistis annotation.")
    ap.add_argument("--check", action="store_true", help="validate without writing")
    args = ap.parse_args(argv)

    bad = 0
    built: dict[str, dict] = {}
    for fn in UNITS:
        unit = fn().build()
        built[unit["path"]] = unit
        own_n = [[[a, b] for a, b in model.normalize(s)] for s in unit["S_N"]]   # root: identity
        errs = model.edge_errors(unit) + model.cn_errors(unit, unit["T_N"], own_n)
        st_cov = (model.coverage(unit["T_F"], unit["S_F"], "lean"),
                  model.coverage(unit["T_N"], unit["S_N"], "nl"))
        loose = model.unlinked(unit)
        for e in errs:
            print(f"  ! {unit['path']}: {e}")
        for side, cov in zip("FN", st_cov):
            if not cov["complete"]:
                missed = [repr(model.u16cut(unit["T_F" if side == "F" else "T_N"], a, b))
                          for a, b in cov["gaps"]]
                print(f"  ! {unit['path']}: T_{side} not covered: {', '.join(missed)}")
        for kind, idxs in loose.items():
            for i in idxs:
                print(f"  ! {unit['path']}: {kind}[{i}] "
                      f"({unit[f'{kind[-1]}_locs'][i]!r}) is in no edge")
        bad += len(errs) + sum(not c["complete"] for c in st_cov) + sum(map(len, loose.values()))
        if not args.check:
            # Drop any stale scaffolded children (`build.py` seeds one per marker/split match) —
            # this annotation is root-only, so nothing should be left on disk that no edge names.
            d = model.unit_dir(ITEM, unit["path"])
            for sub in d.iterdir():
                if sub.is_dir() and (sub / "unit.json").exists():
                    shutil.rmtree(sub)
            model.save(unit)
        print(f"[{'ok   ' if not (errs or loose['S_F'] or loose['S_N']) else 'ERROR'}] "
              f"{unit['path']:<6} {len(unit['S_F'])}F / {len(unit['S_N'])}N regions, "
              f"{sum(map(len, unit['C_N']))} C_N, {len(unit['edges'])} edges, "
              f"F {st_cov[0]['covered']}/{st_cov[0]['total']} N {st_cov[1]['covered']}/{st_cov[1]['total']}")
    if not args.check:
        print()
        from build import show
        show(model.rollup(ITEM))
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
