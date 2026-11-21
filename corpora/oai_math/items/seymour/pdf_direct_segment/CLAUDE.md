# pdf_direct_segment — NL↔Lean faithfulness alignment

Annotate a math paper's NL (definitions, theorems, proofs) as a labelled box tree,
then **align** each definition/theorem against its Lean formalization to surface
faithfulness bugs (where the NL and the Lean say structurally different things).

## Layout
- `tree.json` — the annotation: a tree of **boxes**. Each box has `id`, `label`
  (dotted path, e.g. `formula.atomic-formula.relation`), `pieces` (char spans into
  `chars.txt`), optional `var`/`sym`/`count`/`implicit`. Leaf boxes with no label
  are raw, not-yet-labelled **segments**.
- `chars.txt` — the flat source text; all `pieces` are `[start,end)` offsets into it.
- `schema.json` — single source of truth for the label taxonomy (ISA/HASA/slots).
  Read by both `core.js` and the tools; never duplicate these tables.
- `core.js` — shared tree logic (labels, slots, issues, traversal).
- `lean/` — the Lean formalization. `lean_dict.json` maps a box id → its Lean decl
  (`decls`) and FOL symbol names → Lean meanings (`symbols`).
- `tools/` — the CLI (below). `ui/` + `serve.py` — the browser inspector.
- `doc/align-todo.md` — the alignment design spec (slot↔Lean-target mapping). Read
  it before touching `align*.js`.

## CLI
- **Inspect:** `node tools/inspect.js <id>` (subtree + structural issues),
  `node tools/inspect.js <id> --align` (run the alignment, show findings).
- **Edit** (mutates `tree.json`, header lists all commands):
  `node tools/edit.js <cmd> …` — `set-label`, `set-pieces`, `set-var`, `set-sym`,
  `add`, `rm`, `move`, `wrap`, `add-json`, and `split <id> <off1,off2,…>`
  (cut a one-piece segment at char offsets → first stays, rest become new siblings).
  Compute offsets by slicing `chars.txt`; verify by slicing before you split.

## How alignment works (align.js / align_driver.js / lean_spans.js)
1. NL parses into the FOL box tree; the Lean decl is extracted and **elaborated** to
   an Expr tree. The aligner walks the two **in lockstep against the compiled tree**
   (not surface text): implication↔arrow, ∧↔And, ∉↔`Not(Mem…)`, consulting
   `lean_dict.symbols` at leaves. It **halts** on a genuine shape mismatch.
2. A def/theorem maps by four slots to DIFFERENT parts of the decl: `name`→decl name,
   `inputs`→binder names, `conditions`→binder TYPES, `body`/`conclusion`→the peeled
   body/type. Theorems additionally peel the prenex on both sides.
3. Lean spans are stamped **top-down**: binders use exact parse-tree byte offsets;
   body nodes are rendered back to surface text and located within the parent's span.
   Un-locatable infix ops (`*`,`=`) take the envelope of their located children.

## Working principles (learned, load-bearing)
- **Faithfulness = "exactly the same thing."** `a=b` ≠ `b=a`, `a>b` ≠ `b<a`. The
  strict structural checker is **sound by construction**: every flag is a real (if
  pedantic) infidelity. Do NOT add commutativity/normalization "to be nice" — that
  only reintroduces false positives. Looseness, if ever added, must be a
  meaning-preserving canonicalization applied to BOTH sides, each one auditable.
- **A match must be against an ASSERTED position**, never an assumption. In the
  elaborated tree, assumptions are λ-bound / `Pi`-domain (hypotheses, antecedents,
  the `by_contra` negation); assertions are types inhabited by a constructed term
  (proved `have`s, the goal). Matching an NL claim to an antecedent is a false
  positive.
- **Proofs:** align each NL step-proposition against the TYPE of a `have` (or goal).
  Absence of a match means "couldn't locate / abstain" — **never** "unfaithful"
  (a step can be faithful yet refactored into another lemma, specialized, or
  absorbed into a tactic). Only a positive contradiction justifies "unfaithful".

## Segmentation convention (proofs)
One idea per segment, **no ands** — conjuncts become flat sibling steps, the "and"
tokens stay as their own (commentary) box for coverage. Separate **context-moves**
(introduce a variable, define a term, assume) from **assertions**; split a
premise+conclusion joined by "so"/"thus" into separate segments. Keep piece tiling
gap-free and non-overlapping.

## Proof structure (schema labels)
A proof's structural vocabulary (schema `proof` slot). Every context-extension has a
discharge; only `assume` (and a case split) needs an explicit close.
- **assert** = a `formula` under `proof` — one step/claim; aligns to a Lean `have`
  TYPE (or goal). Most steps are these.
- **openers** (extend the context; all bind an optional name + optional fact):
  - `tactic.let` — fix an arbitrary variable (∀). discharge: ∀. no prerequisite.
  - `tactic.pick` — choose a witness from an ∃ (∃-elim). **consumes a prior ∃**;
    its own label precisely because of that prerequisite. do not fold into `let`.
  - `tactic.define` — abbreviate `name = expr` (a `set`/`let`). no close, ever.
  - **`assumption`** (block) — "suppose P". A BLOCK: children = the assumed
    `formula` P + a nested `proof` (the body under P). Scope is structural (ancestors
    = live binders); steps inside stay **bare** (P stated once, at the block head).
- `tactic.discharge` — the explicit close of an `assumption`; `sym` carries the kind
  (`contradiction` → ¬P/by_contra, else direct → P→…). It reconstitutes the goal, so
  it aligns back to the decl's conclusion.
- **`case-analysis`** (block) of `case` children (each = a hypothesis `formula` + a
  `proof`); carries the **exhaustiveness** obligation (a property of the split, not
  any one arm).

Worked example: `b10` (Lemma 3.2's proof) is built this way — `assumption` block
(b554) = assumed `xⱼyₛ≠0` + a nested `proof` (b555) holding `let τ`, `define Dτ`,
the asserts, and `discharge {contradiction}` (b25). Build blocks with
`edit.js wrap <ids> assumption|proof|case-analysis`; scope = nesting, no link type.

## Aligner for proofs — PHASE 2 (not built)
The scope-threading proof-walk: thread Γ (open binders from ancestors); align each
assert's bare prop against the set of **in-scope assertoric** Lean props (`have`
types / goals — never antecedents/assumptions); emit found / **not-found = abstain**
(never "unfaithful"); at a `discharge` align the discharged ¬P/goal to the decl
conclusion. **Blocker:** `lean_extract` returns the elaborated kernel `Expr`, not a
clean list of `have`-types — Phase 2 must first extract assertoric propositions
(parse the tactic block, or walk the proof term's `let`/`have` nodes).
