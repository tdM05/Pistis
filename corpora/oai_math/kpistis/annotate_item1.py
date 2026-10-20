#!/usr/bin/env python3
r"""item1's K-Pistis annotation, authored and re-runnable.

Every region is NAMED BY THE TEXT IT COVERS and the UTF-16 offsets are computed from that text, so
re-indenting `Proof.lean` or re-wrapping the `.tex` makes this fail loudly (`needle not found`)
instead of quietly sliding the annotation onto the wrong characters. The three levels below are the
SAME construction applied three times; nothing in `model.py` distinguishes them.

    root        T_F = Proof.lean          T_N = statement + proof        regions = proof steps
    root/1.k    T_F = step k              T_N = sentence k               regions = atomic pieces
    root/1.2/…  T_F = one span of step 2  T_N = one span of sentence 2   regions = atomic pieces

The root's `S_F` is NOT the marker partition `build.py` seeds. Two of its regions overlap, on purpose:
`def` and `thm` both include `variable {I J : Type*} [Fintype I] [Fintype J]`, because the paper
states the finiteness of the index sets twice — once before the definition and once inside the lemma —
and each statement has to have something in its own target to point at. That is the whole move this
prototype is about: **what would have been a formal-context item is a span of the target instead**
(README, *No formal context*). Markers cannot express it, which is why they are a seed and this file
is the annotation.

The NL side does not get that move, and `C_N` is the consequence. Every NL region that an edge claims
a formal counterpart for cites the sentences of the paper it has to be read against — `Unit.c`,
written the same way as a region, by the text it covers — each with a reason. Keyed by REGION and not
by unit: an edge names a region, so the context lands on the thing being judged, and the root (whose
own target is the whole paper and so can have no context) is no longer a special case. Those
citations are the places where the paper leaves work to the reader: that 'supported on $T$' was
defined in another paragraph (1.2), that $y_s\ne0$ comes from the reductio and not from anything
nearby (1.7), that 'Therefore' performs three inferences at once (1.8), that `\rank` is never defined
and is written exactly once, in the proof's last line (the root's `thm`), and that $e_s$ is never
defined in the paper at all (1.2, `formula`).

    python3 kpistis/annotate_item1.py            # write
    python3 kpistis/annotate_item1.py --check    # validate without writing
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import model
from model import BOT

ITEM = "item1"
BUILT: dict[str, dict] = {}        # units annotated so far this run, so a child can be cut from its
                                   # parent's spans without a round trip through disk
DERIVED: dict[str, dict] = {}      # skeletons cut this run for units that do not exist on disk yet,
                                   # kept in memory so that `--check` writes nothing at all

# Sentences of the paper that several steps must be read against, named once. These are NEEDLES, not
# stored text: `Unit.c` searches for them and keeps the offsets, so if the `.tex` is re-wrapped this
# file fails with `needle not found` instead of citing the wrong characters.
DEFN = (r"""a matrix supported on
$T\subseteq I\times J$ means a real matrix whose entries outside $T$ are
zero; entries in $T$ are allowed to vanish.""")
MAXRANK = (r"""Suppose that
$D:\R^J\to\R^I$ has maximum rank among all real matrices supported on $T$.""")
CONCL = (r"""Then, for every $x\in\ker D$, every $y\in\ker D^{\mathsf T}$, and every
$(s,j)\in T$, one has $x_jy_s=0$.""")
INDICES = r"$(s,j)\in T$"
DEF_DTAU = r"$D_\tau=D+\tau e_s e_j^{\mathsf T}$"
SUPPOSE = r"$x_jy_s\ne0$"


def paper() -> str:
    """The root's `T_N`: statement + proof, the whole document.

    This is the address space every `C_N` citation indexes into, and it is the only one that makes
    sense — the paper is fixed, so an offset into it is stable in a way an offset into some
    intermediate region is not. `build.py` derives it from the NL `.txt` files and nothing here changes it.
    """
    return model.load(ITEM, "root")["T_N"]


class Unit:
    """One node, written as named regions plus edges between the names."""

    def __init__(self, path: str, **meta):
        self.path = path
        self.base = DERIVED.get(path) or model.load(ITEM, path)
        self.meta = meta
        self.F: dict[str, list] = {}
        self.N: dict[str, list] = {}
        self.C: dict[str, list] = {}          # NL region name -> its citations
        self.edges: list[dict] = []

    def _add(self, side, name, needles, nth):
        text = self.base["T_F" if side is self.F else "T_N"]
        if name in side:
            raise ValueError(f"{self.path}: duplicate region name {name!r}")
        side[name] = [model.find_span(text, n, occurrence=k) for n, k in zip(needles, nth)]
        return self

    def f(self, name, *needles, nth=None):
        return self._add(self.F, name, needles, nth or [0] * len(needles))

    def n(self, name, *needles, nth=None):
        return self._add(self.N, name, needles, nth or [0] * len(needles))

    def c(self, region: str, *needles, why: str, nth=None):
        """One `C_N` citation: prose of the PAPER that NL region `region` has to be read against.

        Addressed exactly like a region — named by what it says, offsets computed — so a citation
        cannot be mis-quoted or drift. What it adds over a region is the `why`: a citation with no
        stated use is not context, it is nearby text. `model.cn_errors` rejects an empty `why`, a
        judged region with no citations, and a citation that overlaps its own region's place in the
        paper.

        Keyed by region and not by unit, so the citation lands on the thing an edge actually judges.
        The chain then makes it count twice over: the root's region `1.2` *is* `root/1.2`'s whole
        `T_N`, so one authored list is the context for the step seen from above and for the same step
        opened up.
        """
        text = paper()
        self.C.setdefault(region, []).append(
            {"spans": [model.find_span(text, n, occurrence=k)
                       for n, k in zip(needles, nth or [0] * len(needles))],
             "why": " ".join(why.split())})
        return self

    def link(self, f, n, v, why, child=None):
        for side, name in ((self.F, f), (self.N, n)):
            if name is not BOT and name not in side:
                raise ValueError(f"{self.path}: no such region {name!r}")
        self.edges.append({"f": f, "n": n, "v": v, "why": " ".join(why.split()),
                           **({"child": child} if child else {})})
        return self

    def build(self) -> dict:
        f_names, n_names = list(self.F), list(self.N)
        for name in self.C:
            if name not in self.N:
                raise ValueError(f"{self.path}: C_N names region {name!r}, which does not exist")
        out = {**self.base, **self.meta, "C_N": [self.C.get(k, []) for k in n_names],
               "S_F": [self.F[k] for k in f_names], "S_N": [self.N[k] for k in n_names],
               "F_locs": f_names, "N_locs": n_names,
               "edges": [{**e,
                          "f": BOT if e["f"] is BOT else f_names.index(e["f"]),
                          "n": BOT if e["n"] is BOT else n_names.index(e["n"])}
                         for e in self.edges]}
        if "/" in self.path:
            # Re-anchor to the parent as just ANNOTATED. The seeded indices are stale by
            # construction: `build.py` numbers the root's regions by the marker partition and this
            # file re-cuts them, so `provenance` has to be derived, not carried over. The equality
            # below is the model's one structural invariant, checked here at the moment it could
            # break and again, from outside, by `check.py`.
            above, name = self.path.rsplit("/", 1)
            parent = BUILT[above]
            e = next(x for x in parent["edges"] if x.get("child") == name)
            out["provenance"] = {"kind": "span", "parent": above, "f": e["f"], "n": e["n"]}
            for target, kind, idx in (("T_F", "S_F", e["f"]), ("T_N", "S_N", e["n"])):
                want = model.region_text(parent[target], parent[kind][idx])
                if out[target] != want:
                    raise ValueError(f"{self.path}: {target} is not its parent's {kind}[{idx}]\n"
                                     f"  parent: {want!r}\n  child:  {out[target]!r}")
        return out


# --------------------------------------------------------------------------- the root
# Category C_1 = "proof step". Its regions are the whole file's worth of declarations and tactic
# steps, each against the sentence it answers.

def root() -> Unit:
    u = Unit("root", title="Lemma 3.2 (Kernels at maximum support rank)",
             category="document", child_category="proof step", done=True)
    var = "variable {I J : Type*} [Fintype I] [Fintype J]"
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
    for m in model.markers(u.base["T_F"]):
        if m["loc"].startswith("1."):
            u.F[m["loc"]] = [m["span"]]

    nl = json.loads((model.CORPUS / "items" / ITEM / "split.json").read_text(encoding="utf-8"))
    u.n("defn", r"""For finite index sets $I,J$, a matrix supported on
$T\subseteq I\times J$ means a real matrix whose entries outside $T$ are
zero; entries in $T$ are allowed to vanish.""")
    u.n("thm", r"""\begin{lemma}[Kernels at maximum support rank]\label{lem:kernel-support}
Let $T\subseteq I\times J$, where $I$ and $J$ are finite.  Suppose that
$D:\R^J\to\R^I$ has maximum rank among all real matrices supported on $T$.
Then, for every $x\in\ker D$, every $y\in\ker D^{\mathsf T}$, and every
$(s,j)\in T$, one has $x_jy_s=0$.""")
    for k, entry in enumerate(nl):
        if k:
            u.n(f"1.{k}", entry["text"])

    # ---- C_N. Every one of these eleven regions is claimed to correspond to Lean, so every one of
    # them cites what it has to be read against. This is the level where per-unit `C_N` had nothing
    # to say — the root's target is the paper, so the root has no context — and where the reader most
    # needs it: these are the thirteen edges you see first.
    u.c("defn", r"Let $T\subseteq I\times J$, where $I$ and $J$ are finite.", why="""
        The finiteness of $I$ and $J$ is asserted HERE as well, inside the lemma, and Lean asserts it
        once — `variable {I J : Type*} [Fintype I] [Fintype J]`. So the `variable` line is in this
        region and in `thm`, and a reader checking either against Lean has to know the other exists
        or the sharing looks like double-counting. The paper saying something twice is what forces
        two formal regions to overlap; this citation is where that is written down.""")
    u.c("thm", r"$\rank D_\tau>\rank D$", why=r"""
        'has maximum rank among all real matrices supported on $T$' is the hypothesis `hmax : ∀ A,
        SupportedOn T A → A.rank ≤ D.rank`, i.e. a ≤ over a set — but the paper never defines `rank`
        and writes `$\rank$` for the first and only time in the proof's last line. The reading that
        makes `hmax` the right formalization is anchored thirteen lines FORWARD, not backward.""")
    u.c("thm", DEFN, why="""
        'supported on $T$' twice in one lemma, defined in the paragraph above. `hD` and `hmax` both
        quantify over it, so the definition is load-bearing for two binders.""")

    # `1.1`–`1.9` are the nine proof steps. Each of these citations is the context for that step's
    # sentence — and by the chain it is the same text as `root/1.k`'s whole `T_N`, so one authored
    # list serves the step seen from here and the step opened up.
    u.c("1.1", CONCL, why="""
        The conclusion this negates. 'Suppose instead' is a pure back-reference: without 'one has
        $x_jy_s=0$' sitting in the lemma, the word 'instead' names nothing and the sentence cannot be
        read at all. It is eight lines and one paragraph break away, so no widening of `T_N` short of
        the whole document would reach it — this is the case `C_F` could not have, and `C_N` must.""")
    u.c("1.1", "a contradiction.", why="""
        Where the reductio opened here is discharged, nine sentences later. Cited because the scope of
        'Suppose instead' is the rest of the proof, and scope is not visible in one sentence.""")
    u.c("1.2", DEFN, why="""
        'is still supported on $T$' is the claim of this sentence, and 'supported on $T$' is defined
        thirteen lines earlier, in the statement paragraph, in a sentence this step has no other
        business with. The formal side needs no such citation — `SupportedOn` is a `def` that the
        region could simply have included — which is exactly the asymmetry: the Lean file can be
        arranged so a definition is adjacent, the paper cannot be rearranged at all.""")
    u.c("1.2", MAXRANK, why=r"""
        What $D$ is. The sentence writes `D` with no introduction; it is the maximum-rank matrix fixed
        by the lemma's hypothesis, which is also why `D_\tau` having to stay supported on $T$ is the
        point of the step rather than an aside.""")
    u.c("1.2", INDICES, why=r"""
        Where $s$ and $j$ come from — the lemma's last binder. Worth recording for a reason the
        formal side makes obvious: `Matrix.single s j 1` is `e_s e_j^{\mathsf T}`, and $e_s$,
        $e_j^{\mathsf T}$ are never defined anywhere in the paper. This is the nearest the document
        comes, so the alignment rests on a convention the reader supplies.""")
    u.c("1.3", DEF_DTAU, why=r"""
        What $D_\tau$ is, from the previous sentence. $D_\tau x=\tau x_j e_s$ is a one-line
        computation FROM that definition, and the Lean region states only the result.""")
    u.c("1.3", r"every $x\in\ker D$", why=r"""
        That $x$ is in $\ker D$ — the lemma's binder, which is what makes $Dx=0$ available and the
        $D$ term of $D_\tau x$ vanish. The paper never shows the cancellation.""")
    u.c("1.4", r"""\[
 D_\tau x=\tau x_j e_s.
\]""", why=r"""
        The equation this concludes from, immediately above. On its own 'Thus $e_s\in\im D_\tau$'
        is not checkable.""")
    u.c("1.4", SUPPOSE, why=r"""
        The step needs $x_j\ne0$ to divide by $\tau x_j$, and that comes from the reductio
        supposition, not from anywhere near this sentence. It is the load-bearing hypothesis of the
        inference and it is nowhere in the sentence that makes it.""")
    u.c("1.5", DEF_DTAU, why=r"""
        What $D_\tau$ is. $Dw=D_\tau w-\tau w_j e_s$ is that definition rearranged.""")
    u.c("1.5", r"Thus $e_s\in\im D_\tau$.", why=r"""
        Why the right-hand side lies in $\im D_\tau$: $D_\tau w$ is there by definition and
        $e_s$ by the previous sentence. The '$\in\im D_\tau$' clause is an inference, and half its
        input is the sentence above.""")
    u.c("1.6", r"""Moreover, for every $w\in\R^J$,
\[
 Dw=D_\tau w-\tau w_j e_s\in\im D_\tau,
\]""",
        why=r"""
        The 'so' makes this sentence a conclusion of the previous one, and the previous one is where
        all the content is: $\im D\le\im D_\tau$ is just that statement re-quantified. Lean states
        the two separately (`hDw`, then `himg`), so the edge joining them is the paper's 'so'.""")
    u.c("1.7", r"every $y\in\ker D^{\mathsf T}$", why=r"""
        That $y\in\ker D^{\mathsf T}$ — the lemma's binder, and the reason '$y$ annihilates
        $\im D$' is true. In Lean that is `hy` plus the transpose/inner-product unfolding; in the
        paper it is this phrase, eleven lines up.""")
    u.c("1.7", SUPPOSE, why=r"""
        $y_s\ne0$ is asserted here flatly, but it is not a hypothesis of the lemma — it follows from
        the reductio supposition $x_jy_s\ne0$. The sentence gives no hint of that, and a reader
        checking `y s ≠ 0` against it would otherwise have no idea where it comes from.""")
    u.c("1.8", r"so the entire old image $\im D$ is contained in $\im D_\tau$.", why=r"""
        One half of 'Therefore': $\im D\subseteq\im D_\tau$.""")
    u.c("1.8", r"Thus $e_s\in\im D_\tau$.", r"$e_s\notin\im D$.", why="""
        The other half: $e_s$ is in the new image and not in the old, so the inclusion is strict.
        'Therefore' performs three inferences at once — inclusion, strictness, and the jump from
        images to ranks — which is why this one word needs two citations and why its Lean counterpart
        is a single `have` with a `sorry` body.""", nth=[0, 0])
    u.c("1.9", MAXRANK, why="""
        The maximality that is contradicted. 'a contradiction' is three words; the fact it
        contradicts is fifteen lines up, in the lemma's hypothesis, and nothing in this sentence
        points at it. `exact absurd (hmax Dτ hsupp) (not_le.mpr hrank)` names `hmax` explicitly —
        the formal side cannot leave it implicit, and the paper does.""")
    u.c("1.9", "is still supported on $T$,", why=r"""
        Why `hmax` applies to $D_\tau$ at all: it has to be supported on $T$, which was step 1.2.
        In Lean this is the `hsupp` argument; in the paper it is nowhere near this sentence.""")

    u.link("hdr", BOT, 1, """
        `import Mathlib`, `open Matrix` and the linter `set_option` are how the file is BUILT, not
        anything it asserts, and the paper has no counterpart to them. ⊥ is the right answer here
        rather than a gap in coverage: the judgment being recorded is 'this says nothing', and it is
        made in the open instead of by leaving the lines out of every region.""")
    u.link("def", "defn", 1, """
        The paper's definition, and the sentence that gives it. `SupportedOn T D := ∀ s j, (s, j) ∉ T
        → D s j = 0` constrains only the entries OUTSIDE `T`, and the implication runs one way, which
        is exactly the sentence's last clause — 'entries in $T$ are allowed to vanish' asks nothing of
        them. The region also carries `variable {I J : Type*} [Fintype I] [Fintype J]`, because 'For
        finite index sets $I,J$' is part of this same sentence; it is shared with the `thm` region
        below, which is legal and deliberate (see this file's docstring).""")
    u.link("thm", "thm", 1, r"""
        The lemma, binder for binder: `hD` and `hmax` are 'has maximum rank among all real matrices
        supported on $T$', `hx` and `hy` are the two kernels (`Dᵀ.mulVecLin` for $D^{\mathsf T}$),
        `hsj` is $(s,j)\in T$, and the goal is $x_jy_s=0$. 'where $I$ and $J$ are finite' is the
        lemma re-stating what the ambient `variable` fixes, so this region includes that `variable`
        line too — otherwise the phrase would have to be matched against a formal-context item, which
        is the thing this prototype exists to avoid.""")
    u.link("tech", BOT, 1, """
        `classical` supplies the `DecidableEq I` / `DecidableEq J` that `Matrix.single` and
        `Pi.single` need and that the statement deliberately does not assume. It changes no goal and
        asserts nothing; the paper never had to name an instance, so there is nothing for it to
        correspond to.""")
    u.link("1.1", "1.1", 1, """
        Opens the reductio the whole proof runs inside. Refined below.""", child="1.1")
    u.link("1.2", "1.2", 1, r"""
        Fixes $\tau$, defines $D_\tau$ and claims it is still supported on $T$ — the three things
        the sentence does, in the order it does them. Refined below; this is the step that motivated
        the prototype.""", child="1.2")
    u.link("1.3", "1.3", 1, r"The displayed identity for $D_\tau x$. Refined below.", child="1.3")
    u.link("1.4", "1.4", 1, "The membership the previous identity yields. Refined below.", child="1.4")
    u.link("1.5", "1.5", 1, """
        The universally quantified chain the sentence displays, as one claim. Refined below.""",
           child="1.5")
    u.link("1.6", "1.6", 1, "The containment of images. Refined below.", child="1.6")
    u.link("1.7", "1.7", 1, """
        The three clauses the sentence asserts about $y$ and $e_s$. Refined below.""", child="1.7")
    u.link("1.8", "1.8", 1, "The strict rank inequality. Refined below.", child="1.8")
    u.link("1.9", "1.9", 1, """
        Closes the reductio `1.1` opened, against the maximality hypothesis. Refined below.""",
           child="1.9")
    return u


# --------------------------------------------------------------------------- the steps
# Category C_2 = "atomic". Every child below is the same object as the root: two targets, regions on
# each, edges with verdicts. The only difference is how much text it is about.
#
# Each step has a `scaffold` region: the `have <name> :` that states the claim and the `:= by sorry`
# that would justify it. Both are how Lean WRITES a claim, not part of what the claim says, so they
# are one ⊥ edge per step rather than being left out of coverage.

SCAFFOLD = """
        `have {name} :` names the claim and `:= by sorry` is where its proof goes. How a claim is
        stated and discharged in Lean; the prose states its claim by writing a sentence and proves it
        elsewhere or not at all. Neither half has anything to correspond to."""


def step_1_1() -> Unit:
    u = Unit("root/1.1", title="step 1.1 — open the reductio", done=True)
    u.f("refine", "refine not_not.mp fun")
    u.f("prop", "x j * y s ≠ 0")
    u.f("name", "hne :")
    u.f("hole", "=> ?_")
    u.n("suppose", "Suppose instead that")
    u.n("ne", r"$x_jy_s\ne0$.")
    u.c("suppose", CONCL, why="""
        The conclusion this negates. 'Suppose instead' is a pure back-reference: without 'one has
        $x_jy_s=0$' sitting in the lemma, the word 'instead' names nothing and the two words cannot
        be read at all. Eight lines and a paragraph break away, so no widening of `T_N` short of the
        whole document reaches it — the case `C_F` could not have, and `C_N` must.""")
    u.c("suppose", "a contradiction.", why="""
        Where the reductio opened here is discharged, nine sentences later. Cited because the scope of
        'Suppose instead' is the rest of the proof, and scope is not visible in two words.""")
    u.c("ne", CONCL, why="""
        Where $x$, $y$, $s$ and $j$ are bound. The formula `x j * y s ≠ 0` has four free names in it
        and this sentence introduces none of them; without the lemma's quantifiers, '$x_jy_s$' does
        not even typecheck as a reading.""")
    u.link("refine", "suppose", 1, """
        The goal here is `x j * y s = 0`. `not_not.mp` turns proving it into refuting its negation and
        the `fun` binds that negation as a hypothesis, leaving `False` to be derived — which is what
        'Suppose instead' does: it opens a reductio, it does not justify one.""")
    u.link("prop", "ne", 1, """
        The supposition itself, written in the prose's own `≠` form. Note WHERE it is written: in the
        target. `Main.lean` has to get this from the `have habsurd1 : ¬(x j * y s ≠ 0) := by intro
        hsuppose1` the segment sits inside, i.e. from formal context, and the quoted-clause rules in
        `faithfulness/README.md` then forbid showing it as `hsuppose1 : x j * y s ≠ 0` because that
        string is in no single line of the file. Here the type ascription on the `fun` binder puts it
        in the proof text, so the span is an offset and there is nothing left to get wrong.""")
    u.link("name", BOT, 1, """
        Lean needs a name for the hypothesis it just introduced. The prose introduces the same
        hypothesis and names nothing.""")
    u.link("hole", BOT, 1, """
        The `?_` is the remaining goal, `False`, that steps 1.2–1.9 fill. Syntax for 'continue here',
        with no counterpart in a paragraph that simply continues.""")
    return u


def step_1_2() -> Unit:
    u = Unit("root/1.2", title="step 1.2 — fix τ and define D_τ", done=True)
    u.f("scaffold", "obtain ⟨τ, hτ⟩ :", "have hsupp :", ":= by sorry")
    u.f("exists", "∃ τ : ℝ, τ ≠ 0")
    u.f("witness", ":= ⟨1, one_ne_zero⟩")
    u.f("set", "set Dτ : Matrix I J ℝ :=")
    u.f("formula", "D + τ • Matrix.single s j (1 : ℝ)")
    u.f("with", "with hDτ")
    u.f("supported", "SupportedOn T Dτ")
    u.n("nonzero", r"For a nonzero real $\tau$,")
    u.n("name", r"""the matrix
$D_\tau=""")
    u.n("rhs", r"D+\tau e_s e_j^{\mathsf T}$")
    u.n("still", "is still supported on $T$,")
    u.c("nonzero", "a contradiction.", why=r"""
        Why τ may be chosen freely: nothing later in the proof constrains it — the final
        contradiction holds for any nonzero τ — which is what makes Lean's `⟨1, one_ne_zero⟩` an
        adequate reading of 'For a nonzero real $\tau$'. That is a fact about the whole proof and
        this clause cannot show it.""")
    u.c("name", MAXRANK, why=r"""
        What $D$ is, since `D_\tau` is named in terms of it: the maximum-rank matrix fixed by the
        lemma. The clause writes `D` with no introduction.""")
    u.c("rhs", r"""the matrix
$D_\tau=""", why="""
        The left-hand side of the equation this is the right-hand side of. It stops exactly where
        this region starts, which is the cleanest demonstration of the no-overlap rule: the two are
        adjacent and `cn_errors` can still prove they do not intersect.""")
    u.c("rhs", INDICES, why=r"""
        Where $s$ and $j$ come from — the lemma's last binder, and ALL the paper offers: $e_s$ and
        $e_j^{\mathsf T}$ are never defined anywhere in it. The reader is expected to supply
        'standard basis vector', and `Matrix.single s j 1` is the formalization committing to that
        reading. The child unit `formula` is where that edge is taken apart.""")
    u.c("still", DEFN, why="""
        'supported on $T$' is defined thirteen lines earlier, in the statement paragraph, in a
        sentence this step has no other business with. The formal side needs no such citation —
        `SupportedOn` is a `def` the region could simply have included — which is exactly the
        asymmetry: the Lean file can be arranged so a definition is adjacent, the paper cannot be
        rearranged at all.""")
    u.c("still", "has maximum rank among all real matrices supported on $T$", why="""
        What 'still' is relative to: $D$ was supported on $T$ to begin with. Lean's `hD` carries that
        and the word 'still' is the paper's entire record of it.""")
    u.link("scaffold", BOT, 1, """
        `obtain ⟨τ, hτ⟩ :` destructures the witness and names it, `have hsupp :` names the claim, and
        `:= by sorry` is where the proof goes. Bookkeeping: the prose fixes a τ without naming a
        hypothesis about it, and states its claim by writing a clause.""")
    u.link("exists", "nonzero", 1, r"""
        `∃ τ : ℝ, τ ≠ 0` is the clause: `τ : ℝ` is 'a real $\tau$' and `τ ≠ 0` is 'nonzero'. The
        proof fixes one such τ and never reads its value, so this is as general as the prose's
        indefinite 'a'.""")
    u.link("witness", BOT, 1, """
        `⟨1, one_ne_zero⟩` is why such a τ EXISTS — take 1. The prose asserts existence without
        exhibiting a witness, and a justification is not part of what is said.""")
    u.link("set", "name", 1, r"""
        `set Dτ : Matrix I J ℝ :=` is the prose's 'the matrix $D_\tau=`: `Matrix I J ℝ` is 'the
        matrix', the name is `Dτ`, and `:=` carries the `=` that defines it.""")
    u.link("formula", "rhs", 1, r"""
        **The edge this prototype was built for.** `Matrix.single s j 1` is the matrix whose only
        nonzero entry is a 1 in position $(s,j)$, i.e. $e_s e_j^{\mathsf T}$; the scalar multiple and
        the sum with `D` are the prose's own. In `Main.lean` the right-hand side of the prose's `=` has
        nothing in the target to link to, because a `pistis_segment`'s target is its claim
        (`SupportedOn T Dτ`) and the defining `set` is formal context — so the edge lands on a quoted
        clause with a line citation instead of on a span. Here the `set` is simply part of the step,
        and the correspondence is span to span.""", child="formula")
    u.link("with", BOT, 1, """
        `with hDτ` names the defining equation so later tactics can rewrite with it. The prose names
        no equation.""")
    u.link("supported", "still", 1, """
        The same predicate as the statement's `SupportedOn T D`, re-applied rather than re-defined —
        which is precisely what 'still supported on $T$' says: the property is the old one, the matrix
        is new.""")
    return u


def step_1_3() -> Unit:
    u = Unit("root/1.3", title="step 1.3 — D_τ x", done=True)
    u.f("scaffold", "have hDτx :", ":= by sorry")
    u.f("lhs", "Dτ.mulVec x")
    u.f("eq", "=")
    u.f("rhs", "(τ * x j) • (Pi.single s (1 : ℝ) : I → ℝ)")
    u.n("and", "and")
    u.n("display", r"\[", ".", r"\]")
    u.n("lhs", r"D_\tau x")
    u.n("eq", "=")
    u.n("rhs", r"\tau x_j e_s")
    u.c("lhs", DEF_DTAU, why=r"""
        What $D_\tau$ is — the previous sentence. Two characters of prose stand for a matrix defined
        one line up, and `Dτ.mulVec x` is only recognisable as them given that definition.""")
    u.c("eq", r"every $x\in\ker D$", why=r"""
        The equality holds only because $Dx=0$, and $x\in\ker D$ is the lemma's binder. This is the
        step's whole content and the paper states it by writing '=': `hDτx`'s `sorry` body is where
        Lean would have to do the cancellation the paper skips.""")
    u.c("rhs", INDICES, why="""
        $e_s$ again, with $s$ from the lemma's last binder and no definition anywhere. `Pi.single s
        1` is the formalization supplying it.""")
    u.c("rhs", r"every $x\in\ker D$", why="""
        $x_j$ — the $j$-th coordinate of the lemma's kernel vector. The subscript is the lemma's
        $j$, not a new name, and nothing in this display says so.""")
    u.link("scaffold", BOT, 1, SCAFFOLD.format(name="hDτx"))
    u.link("lhs", "lhs", 1, r"""
        `Dτ.mulVec x` is $D_\tau x$ — the prose's juxtaposition is matrix-vector application, which
        is what `mulVec` is.""")
    u.link("eq", "eq", 1, r"Equality of vectors in $\R^I$, on both sides.")
    u.link("rhs", "rhs", 1, r"""
        `Pi.single s 1` is the vector that is 1 at `s` and 0 elsewhere, i.e. $e_s$, and `(τ * x j) •`
        is the scalar $\tau x_j$ in front of it. The ascription `: I → ℝ` is Lean fixing which
        function space the basis vector lives in; `Pi.single` alone does not say.""")
    u.link(BOT, "and", 1, """
        A connective: it joins this claim to 1.2's. Lean's `have` is already in sequence after 1.2, so
        the sequencing is carried by position and there is no token to point at.""")
    u.link(BOT, "display", 1, r"""
        `\[`, `\]` and the full stop: how LaTeX presents the equation and how the sentence ends.
        Presentation, not content — and recorded as a ⊥ edge rather than left uncovered, because
        'these characters say nothing mathematical' is itself the judgment.""")
    return u


def step_1_4() -> Unit:
    u = Unit("root/1.4", title="step 1.4 — e_s ∈ im D_τ", done=True)
    u.f("scaffold", "have hes :", ":= by sorry")
    u.f("es", "(Pi.single s (1 : ℝ) : I → ℝ)")
    u.f("mem", "∈")
    u.f("range", "LinearMap.range Dτ.mulVecLin")
    u.n("thus", "Thus $")
    u.n("es", "e_s")
    u.n("mem", r"\in")
    u.n("im", r"\im D_\tau")
    u.n("stop", "$.")
    u.c("es", INDICES, why="""
        $s$ comes from the lemma's last binder, and $e_s$ is undefined in the paper — the third
        region in this annotation to depend on a convention the document never states.""")
    u.c("mem", r"""\[
 D_\tau x=\tau x_j e_s.
\]""", r"$x_jy_s\ne0$", why=r"""
        Everything behind the word 'in'. The display exhibits $e_s$ as $(\tau x_j)^{-1}$ times
        $D_\tau x$, and dividing needs $\tau x_j\ne0$, which comes from τ being nonzero and from
        the reductio supposition. Two citations for one membership symbol, because `hes`'s `sorry`
        body is exactly the work the paper compresses into 'Thus'.""", nth=[0, 0])
    u.c("im", DEF_DTAU, why=r"""
        What $D_\tau$ is, and 'im' — which the paper never defines either; `LinearMap.range
        Dτ.mulVecLin` is the formalization choosing column space over anything else.""")
    u.link("scaffold", BOT, 1, SCAFFOLD.format(name="hes"))
    u.link("es", "es", 1, "The same $e_s$ as in 1.3, written the same way.")
    u.link("mem", "mem", 1, "Membership, on both sides.")
    u.link("range", "im", 1, r"""
        $\im D_\tau$ is the image of the linear map $D_\tau$, and `LinearMap.range Dτ.mulVecLin` is
        the range of that map — `mulVecLin` is the matrix read as a linear map, which is what the paper
        means when it writes $D:\R^J\to\R^I$ for a matrix.""")
    u.link(BOT, "thus", 1, """
        'Thus' marks an inference: this follows from 1.3. Lean's `have` asserts without marking where
        the assertion comes from — the justification is the (here `sorry`-ed) proof, not a token in the
        claim. The `$` is a math delimiter.""")
    u.link(BOT, "stop", 1, "Closing math delimiter and full stop.")
    return u


def step_1_5() -> Unit:
    u = Unit("root/1.5", title="step 1.5 — Dw = D_τ w − τ w_j e_s ∈ im D_τ", done=True)
    u.f("scaffold", "have hDw :", ":= by sorry")
    u.f("forall", "∀ w : J → ℝ,")
    u.f("eqn", "D.mulVec w = Dτ.mulVec w - (τ * w j) • (Pi.single s (1 : ℝ) : I → ℝ)")
    u.f("conj", "∧")
    u.f("mem", "D.mulVec w ∈ LinearMap.range Dτ.mulVecLin")
    u.n("moreover", "Moreover,")
    u.n("forall", r"for every $w\in\R^J$,")
    u.n("display", r"\[", r""",
\]""")
    u.n("eqn", r"Dw=D_\tau w-\tau w_j e_s")
    u.n("mem", r"\in\im D_\tau")
    u.c("forall", r"$D:\R^J\to\R^I$", why=r"""
        What $\R^J$ is here: the domain of $D$, as the lemma fixes it. `∀ w : J → ℝ` reads $\R^J$ as
        the function type, which is right because that is what `mulVec` eats — but the paper writes
        $\R^J$ and leaves the identification to the reader.""")
    u.c("eqn", DEF_DTAU, why=r"""
        The identity displayed here is this definition rearranged and applied to $w$. Without it
        $Dw=D_\tau w-\tau w_j e_s$ is an unexplained assertion, and `hDw`'s `sorry` body is where
        the rearrangement would live.""")
    u.c("eqn", INDICES, why="""
        $w_j$ and $e_s$ use the lemma's $j$ and $s$ — the same two indices, still undefined as basis
        vectors. `(τ * w j) • Pi.single s 1` commits to the reading for the third time.""")
    u.c("mem", r"Thus $e_s\in\im D_\tau$.", why=r"""
        What puts the last term inside $\im D_\tau$: $D_\tau w$ is there by definition, and $e_s$
        is there by the previous sentence. The '$\in$' at the end of the chain is an inference and
        half its input is outside this sentence.""")
    u.link("scaffold", BOT, 1, SCAFFOLD.format(name="hDw"))
    u.link("forall", "forall", 1, r"""
        `∀ w : J → ℝ` is 'for every $w\in\R^J$'; the paper's $\R^J$ is the function type `J → ℝ`,
        which is how `mulVec` takes its argument.""")
    u.link("eqn", "eqn", 1, r"""
        The identity, term for term: `D.mulVec w` is $Dw$, the subtraction is the prose's minus sign,
        and `(τ * w j) • Pi.single s 1` is $\tau w_j e_s$ exactly as in 1.3 with $x$ replaced by
        $w$.""")
    u.link("mem", "mem", 1, r"""
        The second half of the chain. The prose writes $Dw=\dots\in\im D_\tau$, so the subject
        $Dw$ is written once and does duty twice; Lean has to write `D.mulVec w` again, which is why
        this region repeats it and the NL region is only the `\in\im D_\tau` part.""")
    u.link("conj", BOT, 1, r"""
        The sentence is a CHAIN — $Dw = D_\tau w - \tau w_je_s \in \im D_\tau$ — which asserts two
        things with one `\in`, and Lean's `∧` is those two things joined. There is no character in the
        prose that is the conjunction, so the connective itself goes to ⊥ while both conjuncts are
        linked above. `split.json` makes the same call from the other side: segment 1.5's `assert` is
        the whole chain, because it cannot be cut into contiguous pieces.""")
    u.link(BOT, "moreover", 1, """
        A discourse connective ('here is a further fact'), carried in Lean by the `have` simply coming
        next.""")
    u.link(BOT, "display", 1, "Display-math delimiters and the comma the display ends on.")
    return u


def step_1_6() -> Unit:
    u = Unit("root/1.6", title="step 1.6 — im D ≤ im D_τ", done=True)
    u.f("scaffold", "have himg :", ":= by sorry")
    u.f("old", "LinearMap.range D.mulVecLin")
    u.f("le", "≤")
    u.f("new", "LinearMap.range Dτ.mulVecLin")
    u.n("so", "so ")
    u.n("old", r"the entire old image $\im D$")
    u.n("contained", "is contained in")
    u.n("new", r"$\im D_\tau$.")
    u.c("old", MAXRANK, why=r"""
        What 'old' means and what $D$ is: the matrix the lemma fixes, before any $\tau$ perturbs it.
        'Old' is doing the work of a name here and the name is fifteen lines up.""")
    u.c("contained", r"""Moreover, for every $w\in\R^J$,
\[
 Dw=D_\tau w-\tau w_j e_s\in\im D_\tau,
\]""", why="""
        What 'is contained in' is a conclusion of. 'The entire old image' inherits the universal
        quantifier of the previous sentence — this sentence has none of its own, so read alone it
        says neither why the containment holds nor what makes it 'entire'. `≤` between submodules is
        the formalization supplying the quantifier.""")
    u.c("new", DEF_DTAU, why=r"""
        What $D_\tau$ is, four sentences back. $\im D_\tau$ is the only term here that mentions
        the perturbed matrix, and nothing nearby says what it is.""")
    u.link("scaffold", BOT, 1, SCAFFOLD.format(name="himg"))
    u.link("old", "old", 1, r"""
        $\im D$, the image of the original matrix. 'the entire old image' is emphasis on the
        quantifier, which `≤` between submodules already carries.""")
    u.link("le", "contained", 1, """
        `≤` on `Submodule`s IS containment, and it is the containment of the whole subspace, which is
        what 'the entire old image is contained in' asserts.""")
    u.link("new", "new", 1, r"$\im D_\tau$, as in 1.4 and 1.5.")
    u.link(BOT, "so", 1, """
        'so' marks the inference from 1.5. As in 1.4, Lean's `have` states the conclusion and leaves
        the inference to the proof, so there is no token here to align it with.""")
    return u


def step_1_7() -> Unit:
    u = Unit("root/1.7", title="step 1.7 — e_s ∉ im D", done=True)
    u.f("scaffold", "have hker :", ":= by sorry")
    u.f("annih", "(∀ v ∈ LinearMap.range D.mulVecLin, y ⬝ᵥ v = 0)")
    u.f("and", "∧", nth=[0])
    u.f("ys", "y s ≠ 0")
    u.f("so", "∧", nth=[1])
    u.f("notin", "(Pi.single s (1 : ℝ) : I → ℝ) ∉ LinearMap.range D.mulVecLin")
    u.n("onother", "On the other hand,")
    u.n("annih", r"$y$ annihilates $\im D$")
    u.n("and", " and ")
    u.n("ys", r"$y_s\ne0$,")
    u.n("so", "so\n")
    u.n("notin", r"$e_s\notin\im D$.")
    u.c("annih", r"every $y\in\ker D^{\mathsf T}$", why=r"""
        What $y$ is. 'annihilates $\im D$' is $D^{\mathsf T}y=0$ restated in a form the lemma never
        uses — `∀ v ∈ range D.mulVecLin, y ⬝ᵥ v = 0` is that restatement made explicit — and this
        binder is the only thing licensing it.""")
    u.c("and", r"every $y\in\ker D^{\mathsf T}$", r"$x_jy_s\ne0$", why="""
        A conjunction of two facts that come from opposite ends of the document: one is the lemma's
        binder, the other the reductio supposition. The `∧` is the only Lean this word gets, and what
        it joins is both times something cited rather than said here.""", nth=[0, 0])
    u.c("ys", SUPPOSE, why=r"""
        Why $y_s\ne0$. The sentence asserts it as if given, but it is half of the reductio
        supposition — the only place in the proof where it is established, five sentences back.""")
    u.c("ys", INDICES, why="""
        And where the subscript $s$ comes from: the lemma's binder, not this sentence.""")
    u.c("so", r"Thus $e_s\in\im D_\tau$.", why=r"""
        The 'so' is an inference whose unstated premise is that $e_s$ is a basis vector, so that
        $y\cdot e_s=y_s$. That identification is nowhere in the paper; the nearest the document
        comes to committing to it is this sentence's $e_s$.""")
    u.c("notin", MAXRANK, why=r"""
        What $\im D$ is, i.e. what $D$ is. This conclusion is about the ORIGINAL matrix, which is
        the whole point of it, and $D$ is named fifteen lines up.""")
    u.link("scaffold", BOT, 1, SCAFFOLD.format(name="hker"))
    u.link("annih", "annih", 1, r"""
        'annihilates' spelled out: every $v$ in $\im D$ has $y\cdot v=0$. That `y` is in $\ker
        D^{\mathsf T}$ is the theorem's hypothesis `hy`; this clause is the consequence the sentence
        states, and it states it, so it is claimed here rather than assumed.""")
    u.link("and", "and", 1, "Conjunction, on both sides.")
    u.link("ys", "ys", 1, r"$y_s\ne0$, written as `y s ≠ 0`.")
    u.link("notin", "notin", 1, r"""
        $e_s\notin\im D$, with $e_s$ the same `Pi.single s 1` as in 1.4 and $\im D$ the same range
        as in 1.6.""")
    u.link("so", "so", 1, """
        A judgment worth being explicit about. The prose's 'so' is an INFERENCE — the third clause is
        drawn from the first two — and Lean's second `∧` only asserts the three side by side. The
        edge is still 1: the sentence ASSERTS all three (which is why `split.json` lists the first two
        as `assumptions` and the third as the `assert`), and the formalization asserts all three. What
        is not captured is the direction of the reasoning, and no Pistis level claims to capture it:
        the `sorry` under this `have` is where that would be checked.""")
    u.link(BOT, "onother", 1, r"""
        'On the other hand' signals a turn in the argument — the preceding steps grew $\im D_\tau$,
        this one bounds $\im D$. Rhetorical structure, with nothing in the claim to carry it.""")
    return u


def step_1_8() -> Unit:
    u = Unit("root/1.8", title="step 1.8 — rank D_τ > rank D", done=True)
    u.f("scaffold", "have hrank :", ":= by sorry")
    u.f("lhs", "Dτ.rank")
    u.f("gt", ">")
    u.f("rhs", "D.rank")
    u.n("therefore", "Therefore $")
    u.n("lhs", r"\rank D_\tau")
    u.n("gt", ">")
    u.n("rhs", r"\rank D", nth=[1])
    u.n("comma", "$,")
    u.c("lhs", DEF_DTAU, why=r"""
        What $D_\tau$ is. And $\rank$: the paper writes it here for the first time, having said
        'maximum rank' in words in the lemma and never defined either. `Matrix.rank` is the
        formalization choosing a definition the document does not give.""")
    u.c("gt", r"so the entire old image $\im D$ is contained in $\im D_\tau$.", why=r"""
        Half of the strict inequality: the containment, which gives
        $\rank D_\tau\ge\rank D$.""")
    u.c("gt", r"Thus $e_s\in\im D_\tau$.", r"$e_s\notin\im D$.", why="""
        The other half, which makes it STRICT: $e_s$ is in the new image and not in the old, so the
        containment is proper. A single `>` whose justification is three sentences in three different
        places — the largest gap in this annotation between what a region says and what it uses, and
        the reason `T_F` here is a bare `Dτ.rank > D.rank` with a `sorry` under it.""", nth=[0, 0])
    u.c("rhs", MAXRANK, why=r"""
        What $D$ is, and that 'maximum rank' was a claim about this same $\rank$. Without that the
        inequality is a fact about two matrices rather than the contradiction it is about to become.""")
    u.link("scaffold", BOT, 1, SCAFFOLD.format(name="hrank"))
    u.link("lhs", "lhs", 1, r"$\rank D_\tau$ as `Matrix.rank`, the rank of the perturbed matrix.")
    u.link("gt", "gt", 1, "Strict inequality, on both sides.")
    u.link("rhs", "rhs", 1, r"$\rank D$, the rank of the original.")
    u.link(BOT, "therefore", 1, r"""
        'Therefore' marks the inference from 1.4, 1.6 and 1.7 — $\im D_\tau$ contains $\im D$ and
        also $e_s$, which $\im D$ omits. The `have` states the conclusion only. Trailing `$` is a
        delimiter.""")
    u.link(BOT, "comma", 1, "Closing math delimiter and the comma before the final clause.")
    return u


def step_1_9() -> Unit:
    u = Unit("root/1.9", title="step 1.9 — contradiction", done=True)
    u.f("exact", "exact")
    u.f("absurd", "absurd")
    u.f("facts", "(hmax Dτ hsupp)", "(not_le.mpr hrank)")
    u.n("contra", "a contradiction.")
    u.c("contra", MAXRANK, why="""
        What is contradicted, and it is named nowhere in this sentence. Three words of prose stand for
        'this contradicts the hypothesis that $D$ has maximum rank among matrices supported on $T$' —
        the extreme case for `C_N`, since `T_N` here is 'a contradiction.' and the formal side is
        `absurd (hmax Dτ hsupp) (not_le.mpr hrank)`, which names both halves explicitly.""")
    u.c("contra", "is still supported on $T$,", why=r"""
        And why $D_\tau$ is even a candidate for the maximum: maximality is only over matrices
        supported on $T$, so 1.2's claim is what makes the contradiction land. `hsupp` is that claim,
        passed to `hmax` on the formal side.""")
    u.c("contra", "Suppose instead that", why="""
        And what the contradiction discharges — the reductio opened nine sentences earlier. 'a
        contradiction' is the END of a scope whose beginning is not in view, which is `refine
        not_not.mp` closing on the formal side.""")
    u.link("absurd", "contra", 1, """
        `absurd : a → ¬a → b` IS the contradiction, and applied here at `b = False` it closes the
        reductio that 1.1 opened. The whole sentence is three words, so the whole edge is one span.""")
    u.link("exact", BOT, 1, """
        The tactic that supplies the term. Lean needs to be told the goal is being closed; a paragraph
        that stops is already closed.""")
    u.link("facts", BOT, 1, """
        The two contradictory facts: `hmax Dτ hsupp` is the maximality hypothesis applied to `Dτ`,
        which 1.2 showed is supported on `T`, giving `Dτ.rank ≤ D.rank`; `not_le.mpr hrank` is 1.8's
        strict inequality in the form that refutes it. The prose says only 'a contradiction' and
        leaves the reader to find them, so there is nothing in this sentence to align them against.
        A real ⊥: the formalization is more explicit than the paper, and that is visible here rather
        than hidden.""")
    return u


# --------------------------------------------------- one level deeper, on the motivating edge
# Category C_3. Nothing new: `root/1.2/formula` is a unit, built the same way, whose targets are one
# span of 1.2's targets. `doc/K_pistis.md` asks why the depth should be two; it is two here only
# because two is enough for most of item1, and three where an edge is worth taking apart.

def deep_formula() -> Unit:
    u = Unit("root/1.2/formula", title="D_τ's defining expression", done=True)
    u.f("D", "D")
    u.f("plus", "+")
    u.f("scalar", "τ •")
    u.f("single", "Matrix.single s j (1 : ℝ)")
    u.n("D", "D")
    u.n("plus", "+")
    u.n("scalar", r"\tau")
    u.n("outer", r"e_s e_j^{\mathsf T}")
    u.n("delim", "$")
    u.c("D", r"""the matrix
$D_\tau=""", why="""
        The left-hand side of the equation this is the right-hand side of. It stops exactly where this
        target starts, which is the point: `C_N` cites the paper, so 'the rest of my own sentence' is
        expressible as a citation and `cn_errors` can still prove the two do not overlap.""")
    u.c("D", MAXRANK, why=r"""
        And what this $D$ is. The paper introduces it as a map $\R^J\to\R^I$; the Lean side is a
        `Matrix I J ℝ`. Two levels up that identification is invisible — here it is the edge.""")
    u.c("plus", "is still supported on $T$,", why="""
        What the sum has to satisfy, which is the only reason this is a sum at all: the second summand
        is supported at a single position of $T$, so adding it keeps the support inside $T$. The claim
        is the tail of the sentence this formula sits in, not part of the formula.""")
    u.c("plus", DEFN, why="""
        And the definition that makes 'still supported on $T$' a checkable statement about the sum
        rather than a word about it. It is eight sentences back, in the paragraph before the lemma.""")
    u.c("scalar", r"For a nonzero real $\tau$,", why=r"""
        The only place $\tau$ is ever quantified, and the only place its nonzeroness is stated. This
        formula uses the symbol as if it were already in scope; the binder is in the clause before.""")
    u.c("outer", INDICES, why=r"""
        The only introduction $s$ and $j$ ever get. $e_s$ and $e_j^{\mathsf T}$ are not defined
        anywhere in the paper — the notation is assumed — so the edge from `Matrix.single s j 1` to
        $e_s e_j^{\mathsf T}$ is judged against a convention rather than a definition. That is a fact
        about the paper worth recording, and a citation with a reason is where it can be recorded.""")
    u.link("D", "D", 1, "The matrix the statement fixes, unchanged.")
    u.link("plus", "plus", 1, "Addition of matrices, on both sides.")
    u.link("scalar", "scalar", 1, r"""
        The scalar $\tau$ times the matrix. `•` is `SMul`, which for `Matrix I J ℝ` is the entrywise
        scalar multiple the paper means.""")
    u.link("single", "outer", 1, r"""
        $e_s e_j^{\mathsf T}$ is the outer product of two standard basis vectors: the matrix with a
        single 1 in position $(s,j)$ and zeros elsewhere. That matrix is `Matrix.single s j 1`. The
        paper names it by a construction and Mathlib by what it is, so this edge is the one place in
        the step where the two notations genuinely differ — which is why it is worth its own level.""")
    u.link(BOT, "delim", 1, "The closing `$` of the inline formula.")
    return u


UNITS = [root, step_1_1, step_1_2, step_1_3, step_1_4, step_1_5, step_1_6, step_1_7, step_1_8,
         step_1_9, deep_formula]


def derive_child(parent: dict, name: str, **meta) -> dict:
    """A child unit's SKELETON, cut from the parent that is in hand.

    Deriving it from `parent` rather than from disk is what makes the invariant hold by construction:
    `child.T_F` is `region_text(parent.T_F, …)` and `child.T_N` is `region_text(parent.T_N, …)`,
    byte for byte, with no window in which the parent on disk is a version behind. `check.py` verifies
    it again from the outside.
    """
    e = next(x for x in parent["edges"] if x.get("child") == name)
    path = f"{parent['path']}/{name}"
    return {"id": f"{ITEM}/{path}", "path": path, "item": ITEM, "loc": name,
            "category": parent.get("child_category", "atomic"), "child_category": "atomic",
            "provenance": {"kind": "span", "parent": parent["path"], "f": e["f"], "n": e["n"]},
            "T_F": model.region_text(parent["T_F"], parent["S_F"][e["f"]]),
            "T_N": model.region_text(parent["T_N"], parent["S_N"][e["n"]]),
            "C_N": [], "S_F": [], "S_N": [], "edges": [], "done": False, **meta}


def regions_in_paper(unit: dict) -> list[list[list[int]]]:
    """Where each NL region sits in the paper, composed from the units annotated THIS RUN.

    `model.regions_in_paper` does the same thing from disk, which is what `check.py` uses. Here the
    chain has to come from `BUILT`, because `--check` writes nothing and the tree on disk may be a
    version behind — and these are the spans `cn_errors` tests citations against for overlap.
    """
    at, path = [[[a, b] for a, b in model.normalize(s)] for s in unit["S_N"]], unit["path"]
    while "/" in path:
        above = path.rsplit("/", 1)[0]
        parent = BUILT[above]
        up = parent["S_N"][unit["provenance"]["n"]]
        at = [model.lift(spans, up) for spans in at]
        unit, path = parent, above
    return at


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Write item1's authored K-Pistis annotation.")
    ap.add_argument("--check", action="store_true", help="validate without writing")
    args = ap.parse_args(argv)

    bad = 0
    for fn in UNITS:
        if fn is deep_formula:
            # Level 3 exists only because an edge of 1.2 asks for it: cut its targets from the
            # annotated 1.2 above, not from whatever is on disk. Held in memory rather than saved,
            # because `--check` must not touch the tree — writing the skeleton here and the
            # annotation only in the write path left `--check` deleting the unit's regions.
            DERIVED["root/1.2/formula"] = derive_child(BUILT["root/1.2"], "formula")
        unit = fn().build()
        BUILT[unit["path"]] = unit
        errs = model.edge_errors(unit) + model.cn_errors(
            unit, BUILT["root"]["T_N"], regions_in_paper(unit))
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
            model.save(unit)
        print(f"[{'ok   ' if not (errs or loose['S_F'] or loose['S_N']) else 'ERROR'}] "
              f"{unit['path']:<22} {len(unit['S_F'])}F / {len(unit['S_N'])}N regions, "
              f"{sum(map(len, unit['C_N']))} C_N, {len(unit['edges'])} edges, "
              f"F {st_cov[0]['covered']}/{st_cov[0]['total']} N {st_cov[1]['covered']}/{st_cov[1]['total']}")
    if not args.check:
        print()
        from build import show
        show(model.rollup(ITEM))
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
