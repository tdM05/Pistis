#!/usr/bin/env python3
r"""The authored align-then-label annotation of item1, as a re-runnable script.

`gen_datapoints.py` derives the two targets and seeds the obvious spans; everything else — which
region of the Lean claim corresponds to which fragment of the prose, and whether it holds — is a
judgment. Those judgments are kept here rather than only in `align/*/artifacts/`, for two reasons:

  * `gen_datapoints.py --force` resets spans and edges whenever a target changes, and without a
    script the work would have to be redone by hand in the UI each time;
  * spans are UTF-16 offsets, and hand-maintained offsets rot the moment a target is re-indented.
    Here every region is named by the text it covers and the offsets are computed, so a target that
    moves does not silently mislabel — it fails loudly with "needle not found".

Written to be read as the annotation, not as code: one `unit(...)` block per datapoint, each edge a
line saying which formal region matches which NL fragment and why.

Conventions used throughout, so the per-edge reasons can stay specific:

  * A segment's `T_F` is the claim and only the claim. The objects the sentence introduces, and the
    reductio it opens, are `C_F` items (`pistis_proof` seeds them from the `obtain`/`set`/`have` lines
    between this tactic and the previous one), so the clause that introduces an object is linked to
    the item that holds it rather than to a region of the claim.
  * A `C_F` item is a QUOTE of the proof — the clause as the file writes it — so an edge into `C_F`
    is named here by a piece of that clause's text (`u.C("obtain ⟨τ, hτ⟩")`), not by a symbol. The
    unit of context is the clause, not the name: `obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ ≠ 0` is one thing the
    proof does and "For a nonzero real τ" is one thing the prose says, so they get one edge. An
    earlier version split that clause into `τ : ℝ` and `hτ : τ ≠ 0` and gave each its own edge —
    two strings that appear nowhere in the file, against prose that says it once.
  * When several formal things answer ONE fragment of prose, each gets its own edge. There are five
    kinds of endpoint — `S_F`, `C_F`, `S_N`, `C_N`, `I` — and an `R` endpoint may also be a
    `{"parts": […]}` group of formal refs, but a group has no card of its own in the UI (it lands in
    a separate "Combined formal endpoints" bucket, unviewable and uneditable). With every verdict 1
    it buys nothing either: two edges into the same NL span say the same thing, each with its own
    reason. So no edge here uses one.
  * A type ascription is linked to prose only where the prose STATES that type — "$T\subseteq
    I\times J$" for `{T : Set (I × J)}`, "$D:\R^J\to\R^I$" for `{D : Matrix I J ℝ}`, "For finite
    index sets $I,J$" for the `variable` line. A binder whose whole content is typing Lean needs goes
    to ⊥: "every $(s,j)\in T$" says the pair is in `T` and says nothing about where `s` lives, so
    `{s : I}` is not what that clause says.
  * A discourse marker ("and", "Thus", "Moreover,", "so", "Therefore", "On the other hand,") is
    linked to ⊥. It signals that an inference is being made; WHETHER the inference goes through is the
    step's backing, not this claim's content.
  * A clause the segment CONSUMES is not in the segment's unit at all. A segment's `T_F` is its
    single assertion (Atomicity) and its `T_N` is the sentence MINUS the substrings `split.json`
    lists under `assumptions` — the paper's `assert(s_i)` — so a premise has neither a region of the
    claim to answer it nor a region of the prose to sit in. It gets a unit of its own, `asm-<loc>-<k>`,
    whose `T_N` is the clause and whose `T_F` is the type on its `-- @pistis_assumption ("clause",
    TYPE)` marker. That pair is what the paper's Atomic Faithfulness condition quantifies over.
    Only seg-1.7 has any, and the two below are the first assumptions in this corpus to be judged.
    Where a premise was lifted out, a single `…` is left, and it takes a ⊥ edge naming the unit that
    holds it: the segment's claim really does say nothing there, and a reader should be able to see
    where the sentence's premises went rather than find them silently deleted.
    Two earlier shapes are gone. First, the premises were conjuncts of the claim, so that they had
    `S_F` regions to align against — which breaks Atomicity and is what `check_main.py` check 6 now
    rejects. Then they were ⊥-linked fragments of a `T_N` that was still the whole sentence, which
    reads as "the formalization does not say this" about a clause the marker does formalize.
  * LaTeX display delimiters (`\[`, `\]`) and sentence punctuation are linked to ⊥ as presentation.
  * There are no ⊥ `C_F` edges, and that is structural rather than lucky: `C_F` holds only what the
    sentence itself introduces, so every item has prose that introduces it. All four in the item are
    here — "Suppose instead that" ↔ the `have habsurd1` and its `intro`; "For a nonzero real
    $\tau$" ↔ the `obtain`; "$D+\tau e_s e_j^{\mathsf T}$" ↔ the `set`. Seven of the nine segments
    have no context at all.
    The rule it replaced was "whatever the claim needs in order to be read", which has no floor —
    `x : J → ℝ` needs `ℝ`, which needs the field axioms, and stopping at the names that happen to be
    written in `Main.lean` is an artefact of which file the seeder reads, not a principle. Writing a
    name is also not saying what its binder says: "$x_jy_s\ne0$" writes `x` and `j` and says nothing
    about where they live. The theorem's binders therefore belong to the `statement` unit, which
    judges each against the prose that introduces it — once, instead of nine times over against
    prose that merely uses the name.

Usage:  python3 faithfulness/annotate_item1.py [--check]
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
sys.path.insert(0, str(HERE))
from alignment_data import _utf16_len, load_bundle                      # noqa: E402
from check_coverage import check_bundle                                 # noqa: E402
from check_targets import check_item                                    # noqa: E402
from pistis_proof import GAP                                            # noqa: E402

BOT = "⊥"
ITEM = REPO / "items" / "item1"

# This annotation is written against the targets `gen_datapoints.py` derives — in particular against
# a segment's T_F being the claim inside `(stepK : …)` and nothing else. A padded or stale target has
# to stop the run here: carrying on would produce spans over text the prose was never answering.
_stale = check_item(ITEM)
if _stale:
    print(f"annotate_item1: {ITEM.name}'s targets are not what this annotation was written against.")
    for _e in _stale:
        print("    ERROR  " + _e)
    print("    Re-run `python3 faithfulness/gen_datapoints.py items/item1 --force` first.")
    raise SystemExit(1)

# --------------------------------------------------------------------------
# the little bit of machinery: regions named by their text, offsets computed
# --------------------------------------------------------------------------
Needle = "str | tuple[str, int]"


def _locate(text: str, needle) -> list[int]:
    """The UTF-16 `[start, end)` of `needle` in `text`. `(s, k)` picks the k-th occurrence."""
    pat, k = needle if isinstance(needle, tuple) else (needle, 1)
    i = -1
    for n in range(k):
        i = text.find(pat, i + 1)
        if i < 0:
            raise SystemExit(f"annotate_item1: occurrence {n + 1} of {pat!r} not found "
                             f"in:\n{text}")
    start = _utf16_len(text[:i])
    return [start, start + _utf16_len(pat)]


class Unit:
    """One datapoint's annotation under construction."""

    def __init__(self, uid: str):
        self.uid = uid
        self.rel = f"items/item1/align/{uid}"
        self.b = load_bundle(self.rel)
        self.T_F, self.T_N = self.b["T_F"], self.b["T_N"]
        self.cf_items = self.b["C_F"].get("items", [])
        self.S_F: list[list[list[int]]] = []
        self.S_N: list[list[list[int]]] = []
        self.R: list = []
        self.lam: list = []

    # -- regions ----------------------------------------------------------
    def _span(self, side: str, needles) -> list:
        text = self.T_F if side == "S_F" else self.T_N
        spans = sorted(_locate(text, n) for n in needles)
        for (a, b), (c, _) in zip(spans, spans[1:]):
            if c < b:
                raise SystemExit(f"{self.uid}: {side} intervals overlap: {spans}")
        store = self.S_F if side == "S_F" else self.S_N
        for i, existing in enumerate(store):           # one region per distinct text, reused
            if existing == spans:
                return [side, i]
        store.append(spans)
        return [side, len(store) - 1]

    def F(self, *needles) -> list:
        """A region of the formal target, named by the source text it covers."""
        return self._span("S_F", needles)

    def N(self, *needles) -> list:
        """A region of the NL target, named by the prose it covers."""
        return self._span("S_N", needles)

    def C(self, needle: str) -> list:
        """The seeded `C_F` item whose quoted clause contains `needle`.

        Named by its TEXT, like every other region in this file, because a `C_F` item is a quote of
        the proof and has nothing else to be named by. It must match exactly one item: two matches
        means the needle is too short to say which clause is meant.
        """
        hits = [i for i, item in enumerate(self.cf_items) if needle in (item.get("signature") or "")]
        if len(hits) == 1:
            return ["C_F", hits[0]]
        have = [i.get("signature") for i in self.cf_items]
        raise SystemExit(f"{self.uid}: {needle!r} matches {len(hits)} C_F clause(s), need exactly "
                         f"one (have {have})")

    # -- edges ------------------------------------------------------------
    def ok(self, formal, nl, reason: str) -> None:
        """`formal` corresponds to `nl`, faithfully, because `reason`."""
        self.R.append([formal, nl])
        self.lam.append([[formal, nl], [1, reason]])

    def bad(self, formal, nl, reason: str) -> None:
        self.R.append([formal, nl])
        self.lam.append([[formal, nl], [0, reason]])

    # -- output -----------------------------------------------------------
    def write(self, *, dry: bool) -> list[str]:
        data = {**self.b, "S_F": self.S_F, "S_N": self.S_N, "R": self.R, "lambda": self.lam,
                "C_N": [], "I": []}
        errors, _ = check_bundle(data, finishing=True)
        if errors or dry:
            return errors
        art = ITEM / "align" / self.uid / "artifacts"
        for rel, obj in (("formal/S_F.json", self.S_F), ("nl/S_N.json", self.S_N),
                         ("nl/C_N.json", []), ("nl/I.json", []),
                         ("relation/R.json", self.R), ("relation/lambda.json", self.lam)):
            (art / rel).write_text(json.dumps(obj, indent=2, ensure_ascii=False) + "\n",
                                   encoding="utf-8")
        label = "unfaithful" if any(v[0] == 0 for _, v in self.lam) else "faithful"
        (art / "label.txt").write_text(label + "\n", encoding="utf-8")
        (art / "done.txt").write_text("true\n", encoding="utf-8")
        return []


UNITS: list[Unit] = []


def unit(uid: str) -> Unit:
    u = Unit(uid)
    UNITS.append(u)
    return u


# ==========================================================================
# statement — the lemma as stated, against the Lean signature
# ==========================================================================
u = unit("statement")

u.ok(u.F("import Mathlib"), BOT,
     "A library import. It fixes which definitions the names below resolve to, but states nothing.")
u.ok(u.F("open Matrix"), BOT,
     "Opens the `Matrix` namespace so `ᵀ` and `⬝ᵥ` parse. Notation scope only.")

# "For finite index sets I,J" — said twice: once in the prose preamble, once inside the lemma.
idx = u.F("variable {I J : Type*} [Fintype I] [Fintype J]")
u.ok(idx, u.N("For finite index sets $I,J$,"),
     "Two types with `Fintype` instances ARE two finite index sets; `I`/`J` keep the prose's names.")
u.ok(idx, u.N("where $I$ and $J$ are finite."),
     "The lemma restates the finiteness the preamble fixed; the `Fintype` instances carry it once.")

# the definition sentence
u.ok(u.F("def SupportedOn"), u.N("supported on"),
     "Names the predicate the prose is defining; `SupportedOn` is the prose's 'supported on'.")
u.ok(u.F("(T : Set (I × J))"), u.N(r"$T\subseteq I\times J$"),
     "`Set (I × J)` is exactly a subset of the index product, so `T` ranges over the prose's `T`.")
mat = u.F("(D : Matrix I J ℝ)")
u.ok(mat, u.N("a matrix"), "The object being defined: an `I × J` matrix.")
u.ok(mat, u.N("a real matrix"), "`Matrix I J ℝ` has real entries — the prose's 'real'.")
u.ok(u.F(": Prop :="), u.N("means"),
     "The prose's 'means' is a definition, which is what `:=` on a `Prop` declares.")
supp = u.F("∀ s j, (s, j) ∉ T → D s j = 0")
u.ok(supp, u.N("""whose entries outside $T$ are
zero;"""),
     "`(s, j) ∉ T → D s j = 0` for all indices is 'every entry outside T is zero', verbatim.")
u.ok(supp, u.N("entries in $T$ are allowed to vanish."),
     "The definition is a one-way implication: for `(s, j) ∈ T` it constrains `D s j` not at all, "
     "which is precisely the licence this clause states.")

# the lemma
u.ok(u.F("theorem kernel_support"),
     u.N(r"\begin{lemma}[Kernels at maximum support rank]\label{lem:kernel-support}"),
     "The lemma's header; `kernel_support` is its label `lem:kernel-support`.")
u.ok(u.F("{T : Set (I × J)}"), u.N(r"Let $T\subseteq I\times J$,"),
     "The same subset-of-the-product reading as in the definition, now as a theorem binder.")
u.ok(u.F("{D : Matrix I J ℝ}"), u.N(r"$D:\R^J\to\R^I$"),
     "A linear map ℝ^J → ℝ^I given by a matrix; `Matrix I J ℝ` acts that way through `mulVec`, "
     "and the hypotheses below use it only so.")
maxrank = u.N("has maximum rank among all real matrices supported on $T$.")
suppose = u.N("Suppose that")
u.ok(u.F("(hD : SupportedOn T D)"), maxrank,
     "'among all real matrices supported on T' only compares `D` with that class if `D` is in it, "
     "which is what `hD` says.")
u.ok(u.F("(hmax : ∀ A : Matrix I J ℝ, SupportedOn T A → A.rank ≤ D.rank)"), maxrank,
     "'has maximum rank' in that class: every matrix supported on `T` has rank at most `D`'s.")
u.ok(u.F("(hD : SupportedOn T D)"), suppose,
     "'Suppose that' marks what follows as a hypothesis; `hD` is one of the two it introduces.")
u.ok(u.F("(hmax : ∀ A : Matrix I J ℝ, SupportedOn T A → A.rank ≤ D.rank)"), suppose,
     "And `hmax` is the other.")
goal = u.F(": x j * y s = 0")
u.ok(goal, u.N("Then,"), "'Then' marks the conclusion: in a signature, whatever follows the last `:`.")
u.ok(u.F("(hx : x ∈ LinearMap.ker D.mulVecLin)"), u.N(r"for every $x\in\ker D$,"),
     "What the prose says about `x`: that it lies in `ker D`. `LinearMap.ker D.mulVecLin` is the "
     "kernel of `D`'s action, and the quantification is the hypothesis being a theorem binder.")
u.ok(u.F("(hy : y ∈ LinearMap.ker Dᵀ.mulVecLin)"), u.N(r"every $y\in\ker D^{\mathsf T}$,"),
     "Likewise for `y`: membership in the kernel of the transpose's action.")
u.ok(u.F("(hsj : (s, j) ∈ T)"), u.N(r"""and every
$(s,j)\in T$,"""),
     "What the prose says about `s` and `j`: that the pair lies in `T`.")
# The four type ascriptions are NOT what those clauses say — see the convention in the docstring.
u.ok(u.F("{x : J → ℝ}"), BOT,
     "The prose never ascribes a type to `x`; it says only `x ∈ ker D`. Lean has to name the ambient "
     r"space before it can state that membership, and ℝ^J is forced by `D:\R^J\to\R^I` — so this "
     "binder is typing the formalization needs, with nothing in the sentence asserting it.")
u.ok(u.F("{y : I → ℝ}"), BOT, r"The same for `y`, whose ℝ^I is forced by `D^{\mathsf T}`'s shape.")
u.ok(u.F("{s : I}"), BOT,
     "The prose does not say `s ∈ I`. It introduces `s` only as the first component of a pair in "
     r"`T`, and `T\subseteq I\times J` is what makes that component an `I`.")
u.ok(u.F("{j : J}"), BOT, "The same for `j` as the second component.")
u.ok(goal, u.N("one has $x_jy_s=0$."),
     "`x j * y s = 0` is `x_j y_s = 0`; the universal quantification is carried by the binders.")
u.ok(u.F(":= by sorry"), BOT,
     "The proof body. This unit's target is the STATEMENT; the body is what the segments annotate.")

# ==========================================================================
# seg-1.1 — "Suppose instead that x_j y_s ≠ 0."
# ==========================================================================
u = unit("seg-1.1")

sup = u.N(r"$x_jy_s\ne0$.")
u.ok(u.F("x j * y s ≠ 0"), sup,
     "`x j * y s ≠ 0` is `x_j y_s ≠ 0`, the proposition this sentence supposes.")
instead = u.N("Suppose instead that")
u.ok(u.C("intro hsuppose1"), instead,
     "'Suppose … that P' is the `intro`: it is what takes P as given. That is context, not the "
     "claim — the claim is P itself, the supposing is the frame it is stated in.")
u.ok(u.C("have habsurd1"), instead,
     "And 'instead': `have habsurd1 : ¬(x j * y s ≠ 0)` is what is actually being proved, so taking "
     "P as given is taking it in order to refute it. The `intro` above is this `have`'s body.")

# ==========================================================================
# seg-1.2 — "For a nonzero real τ, the matrix D_τ = D + τ e_s e_jᵀ is still supported on T,"
# ==========================================================================
u = unit("seg-1.2")

# The claim is the last clause alone; the first two clauses INTRODUCE τ and D_τ, and what they
# introduce is in C_F (see the module docstring).
still = u.N("is still supported on")
u.ok(u.F("SupportedOn"), still,
     "The same predicate as in the statement, re-applied rather than re-defined — which is what "
     "'still supported on' says: the property is the old one, the matrix is new.")
u.ok(u.F("T"), u.N("$T$,"), "The support set the prose writes `T`, the theorem's own `T`.")
named = u.N(r"""the matrix
$D_\tau=""")
u.ok(u.F("Dτ"), named, "The subject of the clause, under the prose's own name for it, `D_τ`.")
nonzero = u.N(r"For a nonzero real $\tau$,")
u.ok(u.C("obtain"), nonzero,
     "`obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ ≠ 0` is this whole clause: `τ : ℝ` is 'a real τ' and `τ ≠ 0` is "
     "'nonzero'. It fixes one such τ and never looks at its value, so it is as general as the "
     "prose's 'a'. The claim does not mention `τ`, so the clause is answered by the context the "
     "claim is stated in.")
pert = u.N(r"D+\tau e_s e_j^{\mathsf T}$")
u.ok(u.C("set Dτ"), pert,
     "The prose DEFINES `D_τ` here, and the `set` is that definition — `:=` carries the prose's `=`, "
     "and `Matrix.single s j 1` is the matrix with a single 1 at `(s, j)`, i.e. `e_s e_jᵀ`. `with "
     "hDτ` names the equation, which is why the clause and not just the name is what is shown.")

# ==========================================================================
# seg-1.3 — "and  D_τ x = τ x_j e_s."
# ==========================================================================
u = unit("seg-1.3")

u.ok(BOT, u.N("and"),
     "A discourse marker: this fact is conjoined to the previous sentence's. It asserts nothing of "
     "its own, and the conjunction is carried by the two steps both being established.")
u.ok(BOT, u.N(r"\[", r"\]", "."),
     "LaTeX display delimiters and the sentence period. Presentation, not content.")
lhs = u.N(r"D_\tau x=")
u.ok(u.F("Dτ.mulVec x ="), lhs,
     "`mulVec` is the matrix acting on a vector, so `Dτ.mulVec x` is the prose's `D_τ x`.")
u.ok(u.F("(τ * x j) •"), u.N(r"\tau x_j"),
     "The scalar `τ x_j`, scaling by `•`, exactly as the prose multiplies.")
es = u.N("e_s")
u.ok(u.F("(Pi.single s (1 : ℝ) : I → ℝ)"), es,
     "`Pi.single s 1` is the vector that is 1 at `s` and 0 elsewhere — the standard basis vector "
     "`e_s` the prose means.")

# ==========================================================================
# seg-1.4 — "Thus e_s ∈ im D_τ."
# ==========================================================================
u = unit("seg-1.4")

u.ok(BOT, u.N("Thus"),
     "An inference marker. Whether `e_s ∈ im D_τ` really follows from the previous equation is this "
     "step's backing; the sentence's CONTENT is the membership alone.")
es = u.N("$e_s")
u.ok(u.F("(Pi.single s (1 : ℝ) : I → ℝ)"), es, "`Pi.single s 1` is the standard basis vector `e_s`.")
u.ok(u.F("∈"), u.N(r"\in"), "Membership, both sides.")
im = u.N(r"\im D_\tau$.")
u.ok(u.F("LinearMap.range Dτ.mulVecLin"), im,
     "The image of `D_τ` is the range of the linear map it induces, which is what `mulVecLin` names.")

# ==========================================================================
# seg-1.5 — "Moreover, for every w ∈ R^J,  Dw = D_τ w - τ w_j e_s ∈ im D_τ,"
# ==========================================================================
u = unit("seg-1.5")

u.ok(BOT, u.N("Moreover,"),
     "A discourse marker introducing a further fact; it asserts nothing of its own.")
u.ok(BOT, u.N(r"\[", r"\]"), "LaTeX display delimiters. Presentation, not content.")
every = u.N(r"for every $w\in\R^J$,")
u.ok(u.F("∀ w : J → ℝ,"), every, "`J → ℝ` is ℝ^J, and `∀` is the prose's 'for every'.")
chain = u.N(r"Dw=D_\tau w-\tau w_j e_s")
u.ok(u.F("(D.mulVec w = Dτ.mulVec w - (τ * w j) • (Pi.single s (1 : ℝ) : I → ℝ))"), chain,
     "The displayed identity term for term: `mulVec` is the action, `Pi.single s 1` is `e_s`.")
u.ok(u.F("∧ D.mulVec w ∈ LinearMap.range Dτ.mulVecLin"), u.N(r"\in\im D_\tau,"),
     "The prose writes a CHAIN, `Dw = … ∈ im D_τ`, which asserts a second fact about the same "
     "quantity; the second conjunct states it of `Dw`, which the first conjunct equates to that "
     "quantity. Two assertions in the sentence, two conjuncts in the claim.")

# ==========================================================================
# seg-1.6 — "so the entire old image im D is contained in im D_τ."
# ==========================================================================
u = unit("seg-1.6")

u.ok(BOT, u.N("so"),
     "An inference marker: the containment is drawn from the previous sentence. The content is the "
     "containment.")
old = u.N(r"the entire old image $\im D$")
u.ok(u.F("LinearMap.range D.mulVecLin"), old,
     "The image of `D` as the range of its induced map. 'entire' is the whole range, which is what "
     "the unqualified `LinearMap.range` is.")
u.ok(u.F("≤"), u.N("is contained in"),
     "`≤` on submodules IS inclusion, so this is the prose's containment and not a rank comparison.")
new = u.N(r"$\im D_\tau$.")
u.ok(u.F("LinearMap.range Dτ.mulVecLin"), new, "The image of `D_τ`, the same way.")

# ==========================================================================
# seg-1.7 — "On the other hand, y annihilates im D and y_s ≠ 0, so e_s ∉ im D."
# ==========================================================================
# The two assumptions FIRST — they are written above the tactic, and the segment's target is what
# is left of the sentence once they are taken out.
u = unit("asm-1.7-0")

u.ok(u.F("∀ v ∈ LinearMap.range D.mulVecLin"), u.N(r"$\im D$"),
     r"`LinearMap.range D.mulVecLin` is the image of the map $v\mapsto Dv$, which is the prose's "
     r"`\im D`, and 'annihilates' a whole subspace is a claim about every element of it — so the "
     "quantifier and the range together are what this one symbol denotes.")
u.ok(u.F(","), BOT,
     "Lean's separator between a binder and its body. The prose has no token here.")
u.ok(u.F("y"), u.N("$y$"),
     "The same vector, under the same name; `y : I → ℝ` is a theorem binder, judged in the "
     "`statement` unit.")
u.ok(u.F("⬝ᵥ v = 0"), u.N("annihilates"),
     r"`y ⬝ᵥ v = 0` for every `v` in the image IS annihilation of that image: the dot product "
     "vanishing is exactly what it means for `y` to kill a vector. The direction is right too — "
     "the prose says `y` annihilates the image, not the image `y`.")

u = unit("asm-1.7-1")

u.ok(u.F("y s"), u.N("$y_s"),
     r"`y : I → ℝ`, so `y s` is its value at the index `s` — the prose's subscript $y_s$. `s` is "
     "the index fixed by the statement's binders, not a new one.")
u.ok(u.F("≠"), u.N(r"\ne"), r"`≠` is `\ne`.")
u.ok(u.F("0"), u.N("0$"), "The same zero, in ℝ.")

# ==========================================================================
# seg-1.7 — the sentence MINUS those two premises: "On the other hand, … and …, so e_s ∉ im D."
# ==========================================================================
u = unit("seg-1.7")

u.ok(BOT, u.N("On the other hand,"),
     "A discourse marker contrasting this line of argument with the preceding one.")
u.ok(BOT, u.N(GAP),
     r"Where `$y$ annihilates $\im D$` stood. `split.json` lists it under `assumptions`, so it is "
     "an INPUT to this step and not part of what the step asserts; its formalization is the type on "
     "this segment's first `@pistis_assumption` marker and it is judged in the `asm-1.7-0` unit. "
     "The claim says nothing here, which is the correct reading of this gap and not a defect.")
u.ok(BOT, u.N(("and", 2)),
     "The prose's 'and' joins the two premises that have just been lifted out. The claim has no "
     "connective to carry it — and a discourse marker goes to ⊥ in any case.")
u.ok(BOT, u.N((GAP, 2)),
     r"Where `$y_s\ne0$` stood — judged in `asm-1.7-1`. The sentence states it as if given; it is "
     "established only by the reductio supposition five sentences back, which is what makes it an "
     "assumption of this step rather than a claim of it.")
u.ok(BOT, u.N(", so"),
     "An inference marker: the prose DERIVES the claim from the two premises. Which clause follows "
     "from which is this step's backing, not its content.")
u.ok(u.F("(Pi.single s (1 : ℝ) : I → ℝ) ∉ LinearMap.range D.mulVecLin"),
     u.N(r"$e_s\notin\im D$."),
     "`Pi.single s 1` is `e_s` and `LinearMap.range D.mulVecLin` is `im D`, so this is the prose's "
     "non-membership — and it is the WHOLE claim, because it is the whole of what this sentence "
     "asserts once its two premises are set aside. An earlier version made it the third conjunct of "
     r"`(∀ v ∈ …, y ⬝ᵥ v = 0) ∧ y s ≠ 0 ∧ …` so that the premises had an `S_F` region to align "
     "against. That buys alignment by breaking Atomicity — one assertion per segment — and it is "
     "not needed: an assumption's formalization has a unit of its own.")

# ==========================================================================
# seg-1.8 — "Therefore rank D_τ > rank D,"
# ==========================================================================
u = unit("seg-1.8")

u.ok(BOT, u.N("Therefore"),
     "An inference marker: the rank strictly grows because the image did. The content is the "
     "inequality.")
rt = u.N(r"$\rank D_\tau")
u.ok(u.F("Dτ.rank"), rt, r"`Matrix.rank` over ℝ is the prose's `\rank`, applied to `D_τ`.")
u.ok(u.F(">"), u.N(">"), "A strict inequality, both sides.")
rd = u.N(r"\rank D$,")
u.ok(u.F("D.rank"), rd, "The same rank, applied to `D`.")

# ==========================================================================
# seg-1.9 — "a contradiction."
# ==========================================================================
u = unit("seg-1.9")

u.ok(u.F("False"), u.N("a contradiction."),
     "`False` is the contradiction the reductio reaches. The hypothesis it refutes is `step1`, "
     "opened by this proof's `have … : ¬(…) := by intro …`; what makes `False` derivable is this "
     "step's backing, not the content of 'a contradiction'.")


# ==========================================================================
def main(argv=None) -> int:
    dry = "--check" in (argv if argv is not None else sys.argv[1:])
    bad = 0
    for u in UNITS:
        errors = u.write(dry=dry)
        n = len(u.lam)
        print(f"[{'FAIL' if errors else ('would write' if dry else 'ok')}] {u.rel}  "
              f"{len(u.S_F)} S_F / {len(u.S_N)} S_N / {n} edges")
        for e in errors:
            print("    ERROR  " + e)
        bad += len(errors)
    print(f"\n{bad} error(s)" if bad else "\nall units annotated, every edge faithful")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
