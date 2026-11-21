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
premise+conclusion joined by "so"/"thus" into separate segments. A proof-by-
contradiction is one assumption segment ("suppose instead …") + derived steps + a
closing "a contradiction" → maps to Lean `by_contra`. Keep piece tiling gap-free and
non-overlapping.
