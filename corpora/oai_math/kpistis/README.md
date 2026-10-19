# K-Pistis — one alignment primitive, applied at every level

A second, independent prototype for `corpora/oai_math`. It leaves `items/item*/Main.lean`,
`pistis_segment` and `faithfulness/` **exactly as they are** and re-does the same job — "is this
formalization faithful to this paper?" — out of one piece instead of two.

The two prototypes answer different questions and are worth keeping side by side:

| | `faithfulness/` | `kpistis/` |
|---|---|---|
| what a datapoint is | a `pistis_segment`'s claim, plus formal context | a span of a Lean file, nothing else |
| how the proof is cut | the `pistis_segment` tactic, inside the proof | `--| <loc>` comments, outside the proof |
| levels | 2, and the second is a different model | any number, and they are the same model |
| what a label aligns to | targets (`T_F`/`T_N`) *and* context (`C_F`/`C_N`/`I`) | targets, plus a `C_N` per NL region |
| formal context | authored: quoted signatures with citations | none — it goes into `T_F` |
| NL context | authored: quoted prose with citations, per datapoint | authored, as spans into the paper, per NL region |
| where the alignment lives | `items/item1/align/*/artifacts/` | `kpistis/units/item1/**` |

---

## Why

From `items/item1/Main.lean`:

```lean
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ ≠ 0 := ⟨1, one_ne_zero⟩
  set Dτ : Matrix I J ℝ := D + τ • Matrix.single s j (1 : ℝ) with hDτ
  pistis_segment "1.2"
    "For a nonzero real $\\tau$, the matrix
$D_\\tau=D+\\tau e_s e_j^{\\mathsf T}$ is still supported on $T$,"
```

A `pistis_segment`'s target is its **claim** — here `SupportedOn T Dτ`. The `set` line above it, the
line that actually says what `D_τ` *is*, is not part of the target; it is formal context. So the
prose `$D_\tau=D+\tau e_s e_j^{\mathsf T}$` has nothing in the target to align to. The right-hand
side of the paper's own defining equation — the most checkable thing in the sentence, the place where
`Matrix.single s j 1` has to be recognised as $e_s e_j^{\mathsf T}$ or the formalization is wrong —
could only be linked to a *quoted* clause carrying a line citation.

Two further consequences of the target being a claim:

* a `pistis_segment` has to typecheck where it stands, so the things a Lean proof does that are not
  claims — `refine not_not.mp fun hne : x j * y s ≠ 0 => ?_`, `classical`, `with hDτ` — cannot be
  segments, and drop out of the alignment entirely;
* the segmentation lives *inside* the proof, so the proof is written for the annotation.

In `kpistis/` a unit's formal side is **a span of a Lean file**. The `set` line is simply inside
region `1.2`, so the prose that defines `D_τ` links straight to it, span to span:

```
  set Dτ : Matrix I J ℝ :=     ↔   the matrix $D_\tau=
  D + τ • Matrix.single s j 1  ↔   D+\tau e_s e_j^{\mathsf T}$      ← and this edge has a child
```

## No formal context

**This is the design decision the prototype is built around, so here is the argument in full.**

Upstream, a datapoint is (target, context): the claim, plus the `variable` / `obtain` / `set` clauses
you must read the claim against. Here there is no `C_F` and no `I`. (There *is* a `C_N`, for a reason
that is specific to the NL side; see *Natural-language context* below. The symmetry does not hold,
and the first draft of this prototype was wrong to assume it did.) The claim:

> **Anything that would be formal context can instead be part of the target — and should be.**
> If a piece of `T_N` corresponds to a clause of the ambient proof, enlarge `T_F` to include that
> clause. It is text in the same file, usually immediately above. So the context-free form always
> exists.

And it is not merely possible, it is strictly more faithful. A context item is **a quotation with a
citation**: someone transcribes a signature and says where it came from. A transcription can be
mis-cited, re-ordered, paraphrased or silently drift from the file — `faithfulness/README.md`
(*Is it a quote?*) had to ban four separate shapes of bad `C_F` for exactly this reason, and
`faithfulness/check_verbatim.py` and `check_citations.py` exist to police it. A target span cannot be
any of those things, because it is **an offset into the text it is a span of**. There is nothing to
transcribe, so there is nothing to get wrong, so there is no checker needed: `check.py`'s third check
subsumes both of those scripts (see *the chain*, below).

Prose with no formal counterpart does not disappear into an `I` list either; it is an **edge to ⊥**,
which is a judgment the labeler makes in the open, with a reason attached, and which `check.py`
counts.

Two shapes this turns out to need, both visible in `item1`:

* **Overlapping regions.** The paper states that `I` and `J` are finite twice — once before the
  definition of "supported on $T$", once inside the lemma. Lean states it once, in
  `variable {I J : Type*} [Fintype I] [Fintype J]`. So the root's regions `def` and `thm` *both*
  include that line: each sentence has something in its own target to point at. That is the move —
  what would have been one formal-context item cited by two datapoints is one piece of text in two
  regions.
* **Writing the proof so the claim is in the text.** `refine not_not.mp fun hne : x j * y s ≠ 0 => ?_`
  is used rather than `by_contra hne`, because the reductio's supposition — the paper's "Suppose
  instead that $x_jy_s\neq0$" — is then *written in the file* and can be a span. With `by_contra` it
  exists only in the goal state, which is not text and cannot be aligned to.

The honest caveat: nothing *proves* the context-free form always exists. It is a claim about
mathematical writing, which this item does not refute. If some future item needs a fact that is
genuinely not in the file — a Mathlib lemma statement, say — the answer is to put it in the file.
`C_F` can come back if it has to; the point of removing it is to find out whether it has to.

A second caveat, specific to the NL side: enlarging the target is always *possible* but it is not
*free*. The Lean file can be rewritten so the clause you need is adjacent; the paper cannot. The only
tools on the NL side are widening a region and using non-contiguous spans, and both cost precision —
a wider region asserts less exactly, and `" … "` between two pieces is a reading someone has to
accept. In `item1` both were needed and both are visible: `def`/`thm` share the `variable` line, and
`1.3`'s and `1.5`'s NL regions are split (`S_N[1] = [[4,6],[29,30],[31,33]]` — three fragments of one
sentence that answer one piece of Lean). That caveat is what the next section is about: pushed far
enough, it is not a caveat, it is a missing field.

## Natural-language context (`C_N`)

**The asymmetry is real, and `C_N` exists because of it.** Take `1.2`, whose `T_N` is "For a nonzero
real $\tau$, the matrix $D_\tau=D+\tau e_s e_j^{\mathsf T}$ is still supported on $T$,". To check it
you need to know what *supported on $T$* means — and the paper defines it **thirteen lines earlier**,
in a different paragraph, before the lemma even starts. On the formal side the equivalent move is easy
and is exactly what *No formal context* prescribes: rearrange `Proof.lean` so `def SupportedOn` sits
next to the step, widen `T_F`, done. The paper cannot be rearranged, and widening `T_N` until it
reaches the definition would swallow every sentence in between — which is to say it would become the
root. So:

> **`C_F` is deletable because the Lean file is ours to arrange. `C_N` is not, because the paper is
> not.**

What makes this `C_N` different from the upstream one is *how it is stored* and *what it hangs off*.

It is not a transcription with a citation but **spans into the root's `T_N`** — the paper — each with
a reason. And it is indexed **like `S_N`, one list of citations per NL region**, not one list per
unit:

```json
[ [],
  [{"spans": [[29, 167]], "why": "'supported on $T$' is defined thirteen lines earlier, in the
    statement paragraph, in a sentence this step has no other business with. The formal side needs no
    such citation — `SupportedOn` is a `def` the region could simply have included — which is exactly
    the asymmetry."}],
  … ]
```
(one entry per region, in `S_N` order; the `why` is one line on disk, wrapped here to fit)

`[29, 167)` of the paper is "a matrix supported on $T\subseteq I\times J$ means a real matrix whose
entries outside $T$ are zero; entries in $T$ are allowed to vanish."

Per-unit was the first attempt and it had a hole in the worst possible place. **The root's target is
the whole paper**, so the root can have no context at all — every candidate sentence overlaps its own
target — and the root is the view you open the tool on. Hanging context off the region closes that:
an edge is the thing being judged, an edge names an NL region, so every edge has its context at every
level, root included. The chain then makes one authored list do double duty, because
`child.T_N == region_text(parent.T_N, parent.S_N[n])`: the root's region `1.2` *is* `root/1.2`'s whole
`T_N`, so the citations written for that region are the context for the step seen from above **and**
for the same step opened up.

So `C_N` is **authored but not transcribed**: *which* sentences matter is a judgment only a person can
make, and it stays a judgment, carried with its reason. But there is no quoted string to drift from
the paper, no line number to go stale, and nothing for a `check_verbatim.py` to police. The viewer
slices the text out of the paper at render time; it is nowhere on disk.

The original "move it into the target" argument survives as an enforceable rule rather than as an
absence:

> **A `C_N` citation may not overlap its own region's place in the paper.** Text you are *claiming*
> belongs in `T_N`. Text you need in order to *read* the claim is `C_N`.

`check.py` check 9 proves exactly that, using the same `lift`-up-the-chain arithmetic as check 8 —
`model.regions_in_paper` puts each of a unit's NL regions back into the paper — and `--mutate` watches
it catch a citation that quietly cites the prose it is supposed to be context *for*. Three more rules:
`C_N` is parallel to `S_N` (a dropped entry would silently shift every region after it onto its
neighbour's citations), every region some edge **judges** cites something (one item with an honest
reason is a legitimate answer), and every citation needs a reason. Regions that only ever appear in a
⊥ edge are exempt: "Moreover," and `\[…\]` are not claims, so there is nothing to read them against.
In `item1` that is 42 judged regions of 53, carrying 63 citations between them.

Writing them out turned up things about the paper worth recording, which is the point:

* `$e_s$` and `$e_j^{\mathsf T}$` are **never defined anywhere in the paper**. Four regions cite the
  lemma's `$(s,j)\in T$` as the nearest thing there is, and say so — this is the gap that makes the
  alignment to `Matrix.single s j 1` a judgment rather than a reading.
* `\rank` is never defined either, and the paper writes it **only in the proof's last line**. The
  lemma's own `thm` region cites that line: the statement is formalized against a word the document
  explains nowhere and uses once.
* `1.7`'s `$y_s\ne0$` is true only under the reductio supposition five sentences earlier, so its
  `and` region cites two spans from opposite ends of the document.
* `1.8`'s single word "Therefore" performs three inferences at once, so its `gt` region cites three.
* `1.9`'s three words of prose stand in for the entire maximality contradiction — three citations for
  one region, the extreme case: the maximality hypothesis, the claim fed to it, and the supposition
  the contradiction discharges.

## Where am I — derived placement

That is a second thing, and the prototype keeps the two apart by name, on disk and on screen,
because conflating them was the earlier mistake. `C_N` is **authored**: what you must read this
against. *Placement* is **derived**: where this target physically sits.

> **Authored context is a judgment. Derived placement is a computation.**
> A judgment needs a reason attached and a rule it cannot break. A computation reads the files that
> are already being gated and produces the answer by arithmetic — there is nothing to disagree with,
> and nothing to author.

The chain is what makes the arithmetic available. A child's `T_F` is exactly a slice of its parent's
`T_F`, so the inverse map exists: `model.lift` sends intervals of a region's *text* back to intervals
of the text that region is *of*, dropping the characters of the `" … "` separator, which map nowhere.
It composes, and that is the point — `model.ancestry` composes it the whole way up and reports, for
every ancestor of a unit, the span that unit occupies inside it:

```
root/1.2/formula   T_F = `D + τ • Matrix.single s j (1 : ℝ)`
    inside root/1.2        F [[79, 112]]     N [[46, 73]]
    inside root            F [[1745, 1778]]  N [[578, 605]]
                             = Proof.lean      = the paper, `D+\tau e_s e_j^{\mathsf T}$`
```

So the viewer shows, above the formal target, the enclosing step with this target's place in it
marked — and chips step the frame out as far as the whole file. Nothing there is stored, authored or
citable; it is a function of the unit's path. `check.py`'s **eighth** check gates it the only way that
makes sense: re-slice each ancestor at the offsets `ancestry` reports and demand the unit's own target
back, byte for byte. Mis-arithmetic in `lift` would otherwise produce a rail that points at the wrong
characters while looking entirely plausible — injecting a one-character error into `lift` makes the
gate report 22 failures.

Check 9 uses the same arithmetic for a different purpose: the no-overlap rule needs to know where each
NL *region* sits in the paper, which is `model.regions_in_paper` — `lift` composed up the chain, one
step further in than `ancestry` goes.

Prose with no formal counterpart is still not context either way: it is an edge to ⊥, with a reason.

## The model

One node type, used unchanged at every depth (`model.py`):

```
unit = (T_F, T_N, S_F, S_N, C_N, edges)

  T_F    the formal text this node is about           a string
  T_N    the natural-language text it is about        a string
  S_F    regions of T_F           lists of UTF-16 [start, end) intervals; may overlap, may be
  S_N    regions of T_N           non-contiguous (a region's pieces join with " … ")
  C_N    per NL region, the prose THAT REGION         parallel to S_N; each citation is
         must be read against                         {spans, why} — spans into the ROOT's T_N,
                                                      i.e. the paper, with its reason
  edges  [{f, n, v, why, child?}] f, n are region indices or null (= ⊥)
                                  v ∈ {1 holds, 0 fails, null unjudged}
```

There is no `C_F` and no `I`. `C_N` is addressed in the one fixed coordinate system natural language
has here — the paper — so it means the same thing at every depth, and a leaf three levels down cites
the document directly rather than through its ancestors.

A node is **refined** by picking one of its edges and making a child unit out of it:

```
child.T_F == region_text(parent.T_F, parent.S_F[edge.f])      byte for byte
child.T_N == region_text(parent.T_N, parent.S_N[edge.n])      byte for byte
```

The child is a unit, so it has its own regions, edges and children. In `item1`:

```
root                    T_F = Proof.lean (62 lines)       T_N = statement + proof    regions: proof steps
root/1.2                T_F = step 1.2 (3 lines)          T_N = sentence 1.2         regions: atomic
root/1.2/formula        T_F = `D + τ • Matrix.single…`     T_N = `D+\tau e_s e_j…`    regions: atomic
```

Nothing in `model.py`, `check.py` or `ui/` branches on the level. `doc/K_pistis.md` observes that
there is "no principled reason" for the depth to be 2 and calls it a hyperparameter chosen for human
understanding; here depth is **per branch**, and it is 3 on exactly the one edge that is worth taking
apart.

### The chain

Follow any leaf upward and every step is an offset, never a transcription, so a leaf *is* a quotation
of `Proof.lean` and of the NL source `.txt` files — verifiable by composing slices. This is the one invariant the
whole design rests on, and `check.py` re-derives it from the files on every run.

### ⊥, and why text is never just left out

An edge to ⊥ means *the labeler says this text has no counterpart on the other side*, with a reason.
`with hDτ` names an equation the paper never names; `⟨1, one_ne_zero⟩` is why a nonzero real exists,
which the paper does not bother to say. Both are ⊥ edges with reasons, not omissions — because
"nobody looked at it" and "someone looked and it corresponds to nothing" are different claims, and
only the second one is evidence.

Coverage is what makes the difference enforceable: every **significant** character of both targets
must be in some region, and every region must be in some edge. Significant means non-whitespace, and
on the Lean side comments are exempt too (`model.significant`) — a comment is not something the
formalization asserts, so demanding an NL counterpart for one would make every explanatory note
either a lie or a ⊥ edge. The `--|` markers are comments, so this exempts them as well.

### Order and coverage are reported, not enforced

`doc/Pistis_orders.md` is the reason. First-Order Pistis gets coverage and order *free* from a strict
tiling rule. The price of regions that may overlap, skip and re-order — which *No formal context*
above requires — is that both become things an oracle has to decide. So coverage is a number on the
screen next to the gaps it is made of, and order disagreements are **crossings**: pairs of edges
whose formal order and NL order disagree, computed from where regions start *in the text* (not from
the order someone drew them in), drawn as crossing ribbons, and left to the reader. `item1` has none.

### Seeded vs. judged

The **matching** may be seeded: the `--|` markers are the formalizer's own claim about which step
answers which sentence, and that claim is part of what is being checked, so `build.py` writes it down
as edges with `v: null`. The **verdict** may not be seeded — that would be the tool grading its own
homework. A null stays null until a human writes a reason next to it, `model.edge_errors` rejects a
verdict with no reason, and a node with any open edge rolls up as `NaN` rather than `faithful`.

## Markers

`Proof.lean` is a plain Lean file — no imported tactics, no `pistis_segment`, nothing that has to
elaborate for the annotation's sake. The cut is a comment:

```lean
--| 1.2
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ ≠ 0 := ⟨1, one_ne_zero⟩
  set Dτ : Matrix I J ℝ := D + τ • Matrix.single s j (1 : ℝ) with hDτ
  have hsupp : SupportedOn T Dτ := by sorry
```

A `--| <loc>` line opens a region that runs to the line before the next marker (or EOF), trimmed to
its first and last non-whitespace character. Code above the first marker is rejected — it would be
silently exempt from coverage — so the file's own header comment is all that may live there.

The markers are **a seed, not the truth**: they give `build.py` a partition of `T_F`, in the same way
`split.json` gives it a seed for `S_N`. The authored annotation may re-cut the file into regions that
overlap (`def`/`thm`) or that markers simply cannot express. What is on disk in `S_F.json` is the
annotation; the markers are where it started.

The bodies are `sorry`. The *proof* of each step is not what is being aligned — its statement is —
and a 400-line Mathlib development would bury the thing this prototype is about. `check.py --lean`
elaborates the file and tolerates exactly the `declaration uses 'sorry'` warning, so the statements
are still machine-checked to be well-typed Lean about the right objects.

## Files

| | |
|---|---|
| `model.py` | the primitive: UTF-16 spans, regions, coverage, edges, unit IO, `status`, `rollup`, marker parsing, `lift`/`ancestry`, `cn_text`/`cn_errors` |
| `items/item1/Proof.lean` | the formal side: plain Lean, `--|` markers, `sorry` bodies |
| `build.py` | seeds a tree — root targets, `S_F` from markers, `S_N` from `split.json`, edges where locs agree — and scaffolds a child per refinable edge (`C_N` left empty on purpose) |
| `annotate_item1.py` | `item1`'s authored annotation: 11 units, 69 edges, 63 `C_N` citations on 42 regions, every region and citation named by the text it covers |
| `check.py` | the gate: nine checks, plus `--lean` and `--mutate` |
| `ui/` | the viewer: `serve.py`, `index.html`, `app.js`, `style.css` |
| `units/item1/**` | the annotation on disk — one directory per unit, children as subdirectories |

A unit directory holds exactly seven files, and `check.py` fails if it holds an eighth:

```
units/item1/root/   unit.json  T_F.lean  T_N.tex  C_N.json  S_F.json  S_N.json  edges.json
units/item1/root/1.2/             the same seven
units/item1/root/1.2/formula/     the same seven
```

so `ls -R` is a readable picture of the tree, and a `C_F.json` appearing anywhere would mean the
thing this prototype removed had grown back. (That is a real mutation in `--mutate`.)

## Running it

```sh
cd corpora/oai_math

python3 kpistis/build.py item1              # seed from Proof.lean + split.json (--force to re-seed)
python3 kpistis/annotate_item1.py           # write the authored annotation (--check to validate only)
python3 kpistis/check.py                    # the gate
python3 kpistis/check.py --lean             # ... and elaborate Proof.lean (needs lake)
python3 kpistis/check.py --mutate           # ... and check the gate against 13 broken copies
python3 kpistis/ui/serve.py                 # then open http://localhost:8010
```

The three steps are reproducible in that order from an empty `units/`: `build.py --force` then
`annotate_item1.py` reproduces the tree on disk byte for byte.

### The gate

```
1. spans        every interval nonempty, in bounds, not splitting a surrogate pair
2. edges        real region indices, no ⊥↦⊥, v ∈ {0,1,null}, judged edges have a reason,
                ⊥ edges have no child
3. the chain    every child's T_F/T_N is EXACTLY its parent's region text
4. the roots    root T_F == Proof.lean; root T_N == nl_statement + "\n\n" + nl_proof
5. coverage     every significant character is in a region; every region is in an edge
6. the tree     edges that name a child have one; children are named by an edge
7. no C_F       a unit directory holds exactly the seven files of the model
8. placement    `ancestry` locates a unit inside every ancestor; re-slicing each ancestor at those
                offsets must give the unit's own target back
9. C_N          C_N is parallel to S_N; every NL region some edge JUDGES cites some prose; every
                citation is in-bounds spans into the paper with a reason; and no citation overlaps
                where its own region sits in the paper
```

`--mutate` answers "who checks the checker": the gate is re-run against scratch copies of the tree
with one thing wrong in each — a child target retyped instead of sliced, a span slid by one
character, an edge pointing at region 999, a verdict with no reason, a dropped region, a hand-written
`C_F.json`, a judged region left with no `C_N`, a `C_N` no longer parallel to `S_N`, a citation with
no reason, a citation that quietly cites the prose it is supposed to be context *for*, a ⊥ edge given
a child, the root's `T_F` edited away from `Proof.lean` — and each one must make it FAIL. A gate
nobody has watched fail is not evidence of anything.

The fourteen mutations are mutations of the *tree*, so they exercise checks 1–7 and 9. Check 8 is
arithmetic, and no edit to the files on disk breaks it alone — breaking the chain breaks check 3
first. It was watched to fail the other way, by mutating the code: `+1` on every interval
`model.lift` returns makes the gate report 22 failures, and restoring it returns to a clean run.

### The viewer

One page, which renders **a unit** — whichever unit. `T_F` on the left, `T_N` on the right, the
matching drawn between the panes as a ribbon, and one edge at the bottom.

**One edge at a time, including at the bottom.** Nothing is highlighted until you hover it. Hovering
a span lights that edge's two regions, draws its ribbon — solid for a verdict of 1, red with a ✗ for
0, dashed for unjudged, a short stub ending in ⊥ for an edge to nothing — and fills the strip at the
bottom with **that edge and nothing else**: its two region texts in full, its verdict, its reason.
`j`/`k` walk the others, so every edge is still reachable.

This replaced a table of all thirteen edges, six columns wide. Thirteen rows of region text and
reasons is the annotation *dumped out*; it competes with the two targets it is supposed to explain,
and it is not something a reader can act on. One edge is a claim you can agree or disagree with.
(Two things are still shown unprompted, because they are facts rather than claims: text in no region
at all is greyed, which is what coverage exempts, and a lit run is striped where two regions overlap.)

**Click to pin, then two buttons.** A click pins the edge and scrolls the other pane to its far end;
the header's `▾ deeper` then loads that edge's child **in the same widget**, and `▴ back` returns.
`Esc` unpins (and, unpinned, goes back); `→`/`Enter` and `←`/`u` are the buttons. A pinned edge that
*can* be refined shows a static `▾ refinable — 1.2`. There is no tree to aim at: the pinned edge is
the thing you are acting on, so the action is a button.

That the child renders in the same widget is the whole claim, made visually: the page does not know
whether it is showing a 62-line file against a lemma or three tokens against half a formula.

**Two rails, labelled differently because they are different things.**

* Above `T_F`: **where** — the enclosing step, dimmed, with this unit's target marked in place, and
  chips to step the frame out to `Proof.lean`. Derived, never authored. Empty at the root.
* Above `T_N`: **`C_N`** — the sentences of the paper this unit's NL regions must be read against,
  one clamped line each, each with its reason on hover (and in a toast on click). Authored, but
  sliced out of the paper by offset rather than transcribed. **Never empty, at any level**, which is
  the point of hanging it off the region: hover or pin an edge and that edge's citations are marked
  and opened up in place, and the edge card at the bottom carries its own copy, under `T_F` and
  `T_N`. The rail's height is fixed rather than capped, so marking one never moves the pane below.

`context` in the header hides both.

The NL side is LaTeX. A region that contains a *whole* formula gets it typeset with KaTeX; a region
that **cuts into** a formula — as `$D_\tau=` / `D+\tau e_s e_j^{\mathsf T}$` does, which is the
example this prototype was built for — shows its source in monospace instead. Nothing is ever
re-flowed to make the typesetting prettier: the characters on screen are the characters the spans
index. `source` in the header turns typesetting off entirely.

The UI can write exactly two things: an edge's verdict and reason, and a unit's `done` flag. It
cannot draw a span and it cannot add a `C_N` citation. Both are authored in `annotate_item1.py`,
where they are named by the text they cover and the offsets are computed — a span drawn by dragging
is a span nobody can re-derive, and one that cannot be re-derived cannot be re-checked after the file
is re-indented.

## Where `item1` currently stands

```
11 units, 69 edges, 63 C_N citations on 42 of 53 NL regions, rollup = faithful
root               13 regions F / 11 N, 13 edges (2 ⊥)   F 1036/1036   N 811/811   21 C_N
root/1.1 … 1.9     1–7 regions a side, 3–7 edges each    complete coverage    3–6 C_N each
root/1.2/formula   4 F / 5 N, 5 edges                    F 24/24   N 24/24       6 C_N
```

Every edge is judged (`v = 1`) with a written reason, and there are no crossings anywhere. 27 of the
69 edges are ⊥ edges, which is the interesting number: 16 are places where Lean says something the
paper does not (`import Mathlib`, `classical`, `with hDτ`, the `have`-scaffolding of each step, the
witness `⟨1, one_ne_zero⟩`), and 11 are places where the paper says something Lean does not (the
connectives — "Moreover,", "On the other hand,", "Therefore" — the `\[…\]` display delimiters, and
one stray `$`). Nothing is silently dropped on either side; each of those 27 carries a sentence
saying why it corresponds to nothing.

## What a prototype has not settled

* **Is `Proof.lean` faithful enough to be interesting?** Its step bodies are `sorry`, so what is being
  aligned is the *statements* of the nine steps. The alignment question for a completed proof is the
  same question — the regions get bigger — but nobody has tried it here.
* **Who draws the regions.** Right now: a person writing Python, naming spans by their text. That is
  deliberate (it is re-derivable and it fails loudly), but it is not a labelling workflow.
* **Depth as a hyperparameter.** `K_pistis.md` says depth should be chosen for human understanding.
  Depth 3 on one edge is an existence proof, not a policy. What makes an edge *need* refining?
* **Overlap.** `def`/`thm` overlapping is the right answer for "the paper says it twice", but overlap
  also quietly weakens coverage as evidence: a region can cover text it does not really assert
  anything about. Crossings are reported; overlap is not.
* **Whether the asymmetry is principled or just convenient.** `C_N` exists and `C_F` does not,
  because the Lean file is ours to arrange and the paper is not. That argument is sound as far as it
  goes, but it means the formal side still records nothing about *what was used*: a labeler at
  `root/1.2/formula` can see the `set` line in the rail above, and nothing records that they relied
  on it. If that turns out to matter, the honest answer is a dependency edge inside the tree —
  pointing at a span of `T_F` by the same arithmetic `C_N` uses on the paper — not a quotation.
* **`C_N` has no coverage rule.** Regions must cover their target; citations need not cover anything,
  so "the labeler cited one convenient sentence and ignored the hard one" is not something the gate
  can see. Per-region non-emptiness, parallelism with `S_N`, a reason each, and no-overlap are the
  only enforceable rules found so far — and the first of those is why `C_N` moved from the unit to
  the region: "this unit has context somewhere" was satisfiable by one citation for eleven regions,
  and at the root it was not satisfiable at all.
* **One item.** Everything here is `item1`. `build.py` is item-generic; `annotate_item1.py` is not,
  and is not meant to be.
