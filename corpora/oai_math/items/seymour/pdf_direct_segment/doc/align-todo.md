# Align TODO — map the WHOLE definition to Lean, automatically

The end goal: given a FOL `definition`/`theorem` box and its associated Lean decl,
**automatically map every part of the annotation to the corresponding part of the
Lean side.** Not just the body. Every slot. The Lean binders, the binder types, the
definiendum, the body — all of it is a target the annotation maps onto.

Right now `align_driver.js` (lines 50–58) aligns **only** the `body` slot against the
peeled Lean body and throws away `name`, `inputs`, `conditions`. That is the bug.

---

## What a `definition` must map (all four slots)

A Lean `def` has the shape:

```
def <Name> {implicit type params} [instance binders] (explicit binders) : <Prop> :=
  <body>
```

Example — `b14` ↔ `SupportedOn`:

```lean
def SupportedOn {I J : Type*} [Fintype I] [Fintype J]
    (T : Set (I × J)) (D : Matrix I J ℝ) : Prop :=
  ∀ s j, (s, j) ∉ T → D s j = 0
```

The FOL `definition` box has slots `name`, `inputs`, `conditions`, `body`. Each maps
to a DIFFERENT part of the Lean decl:

| FOL slot       | Lean target                                   | b14 example |
|----------------|-----------------------------------------------|-------------|
| **name**       | the **definiendum** (decl name)               | `b60 "supported on"` ↔ `SupportedOn` |
| **inputs**     | the **binders** (type params + explicit args) | `b58 {I,J,T}` ↔ `{I} {J} (T) (D)` |
| **conditions** | the **binder TYPES / instance binders**       | `b61` {finite I, finite J, matrix, T⊆I×J} ↔ `[Fintype I] [Fintype J] (D : Matrix I J ℝ) (T : Set (I×J))` |
| **body**       | the **body** (after peeling binders)          | `b90` ↔ `∀ s j, (s,j) ∉ T → D s j = 0` |

Mapping = writing the Lean span onto the box (same mechanism already used for body:
`spans[n.fol] = {file,start,end}`). Every slot, every leaf, gets its Lean span.

---

## TODO 1 — align `name` ↔ definiendum
- The `name` box maps to the decl's own name (`assoc.decl` last component, e.g.
  `SupportedOn`).
- Map its span to the `def <Name>` occurrence in the source.
- Finding if the names clearly disagree (optional; low priority).

## TODO 2 — align `inputs` ↔ Lean binders
- Peel ALL binders of the decl (type params `I J`, instance `[Fintype …]`, explicit
  `T D`) — already available via `peelTypeBinders` / `peelBinders`.
- Map each FOL input term to its Lean binder **by name** (FOL input `I` ↔ binder `I`,
  `T` ↔ binder `T`). Name-based so reordering doesn't false-flag.
- Map each matched input's span to the binder.
- Findings:
  - FOL input with no Lean binder → "input present in NL, absent in Lean".
  - Lean explicit binder with no FOL input → "Lean binds X, NL has no input for it".
    (This is the real b14 finding: Lean has explicit `D` — the matrix being
    defined — which the NL inputs {I,J,T} do not list.)

## TODO 3 — align `conditions` ↔ binder types / instance binders
- Each `condition` is a formula that constrains an input. It maps to the **type of a
  binder** (or an instance binder), NOT to a body node:
  - "finite index set I" ↔ `[Fintype I]`
  - "a (real) matrix" ↔ `D : Matrix I J ℝ` (the `ℝ`/`Matrix` in D's type)
  - "T ⊆ I × J" ↔ `T : Set (I × J)`
- This is exactly what `verifySort` + the `typeBinders` (binder→typeConsts) were built
  for — but currently ONLY the body alignment uses them. Conditions must use them too.
- Map each condition's span to the binder type it discharges against.
- Findings:
  - condition with no matching binder type → "NL condition has no Lean counterpart".
  - binder type with no condition → "Lean binder type X is unstated in NL conditions".

## TODO 4 — body alignment: KEEP the halt-on-shape-mismatch behavior
- The structural walk in `align.js` is correct: when FOL shape ≠ Lean shape at a node
  (e.g. FOL `∧` vs Lean `∀`), it HALTS and reports "structures differ here". This is
  the robust behavior. **Do NOT** add type-vs-prop leniency into the body walk to make
  the ∧ "pass" — that masks real divergence.
- Rationale: the `real(v3) ∧ ∀v5(…)` vs `∀ s j, …` case is a GENUINE structural
  difference IN THE BODY (NL put `real` in a body conjunction; Lean put it in binder
  D's type). That belongs to the inputs/conditions alignment (TODO 2/3), not a body
  hack. Once conditions handle `real`↔D-type, the body side is just `∀v5(…)` ↔
  `∀ s j, …`, which aligns cleanly and then exposes the real v3 = D-vs-T coreference
  bug via the var-consistency pass.

## TODO 5 — findings message: show the FULL label path, no hardcoding
- `align_driver.js humanFinding()` currently regex-scrapes the note and HARDCODES
  `NL=∧`, `NL=¬`, `NL=∀`, etc. It breaks for any shape not in that short list.
- Replace with the box's **full concrete label path** from `core`, e.g.
  `body.formula.compound-formula.connective.conjunction`, plus the structural note.
- Message shape: `<full.label.path>: this object is a <conjunction>, Lean counterpart
  is a <forall> — structures differ`. Generic over all labels, no per-symbol table.
- The NL text is already shown in the card's NL block, so the message must NOT repeat
  the NL text (already fixed — the `${nl}:` prefix was dropped).

## TODO 6 — SHOW the Lean being compared against (source + elaborated + path)
- In the align panel AND in every finding, display:
  1. the **Lean file path + location** being mapped to — e.g.
     `lean/MaxSupportKernel.lean:12` (the decl), and for a finding the char offsets
     of the specific Lean span the mismatch is against. The path is already known
     (`deriveLeanRel(assoc)` + the `spans[]` start/end). Surface it, don't hide it.
  2. the **source** Lean decl verbatim (`def SupportedOn (T : …) (D : …) : Prop := ∀ s j, (s,j) ∉ T → D s j = 0`), and
  3. the **elaborated / compiled** term actually aligned against (from
     `.lean_cache/…SupportedOn.json`) — pretty-printed readably, e.g.
     `∀ s j, ¬ (s,j) ∈ T → D s j = 0`, so the user sees what the aligner sees
     (`Not`, `Membership.mem`, `Prod.mk`, instance args, peeled binders).
- Why: the aligner does NOT compare against the surface text — it compares against the
  elaborated tree. The user must be able to see that elaborated form AND where in the
  Lean file it lives to understand a finding (e.g. why `∉` shows up as
  `Not (Membership.mem …)` at `MaxSupportKernel.lean:12`).
- Each finding shows: the FOL object's full label path (TODO 5) + the Lean file path
  & span it was compared against + the structural note. Both "paths" (label path and
  Lean file path) appear.

---

## Design decisions (locked)
- Inputs/conditions matching is **by name**, not positional (robust to reordering;
  surfaces the "NL input T vs Lean binder D" discrepancy cleanly).
- Body walk **halts** on genuine shape mismatch (robust; no type-vs-prop leniency in
  the body).
- Type-vs-prop discharge (sort predicate ↔ binder type) lives in the **conditions**
  alignment, where it belongs — not smuggled into the body walk.
- Findings name the object by its **full label path**, generically.

## Theorems (for completeness — same principle)
- A `theorem` has `formula` + `proof`. The `formula` maps to the Lean decl's TYPE (the
  statement); align the whole formula box against `normType` (already done).
- `proof` → proof term alignment is OUT OF SCOPE for this pass; note it as future work.
