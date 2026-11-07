# Review — "supported on" definition (b14)

Segment: *"For finite index sets I, J, a matrix supported on T ⊆ I × J means a real
matrix whose entries outside T are zero; entries in T are allowed to vanish."*

Reviewed via `node tools/inspect.js b14`. **Structural validation: 0 issues** in the
whole b14 subtree (every box well-formed per schema). The problems below are
*semantic* ("which token / which variable"), which is why the checker passes.

## Overall
Good work. Shape is correct: `definition` = name + inputs + conditions + body, with
implicit ∧ / → and coreference links used correctly. Only two real errors + minor notes.

## Issues to fix

### 1. (biggest) Universal `b95` — the word "entries" is mis-split
Current: `b97 [sym.var] "entrie"` + `b98 [sym.∀] "s"`.
- The ∀ in "entries … are zero" is **implicit** (no glyph) — it should be an
  **implicit** quantifier box, like the other implicit symbols.
- The bound variable is **"entries"** (the whole word), label `variable-symbol`.
- Splitting "entrie"/"s" to manufacture a ∀ glyph out of the plural "s" is wrong.
Fix: make `b98` (∀) implicit with no span; give the variable-symbol the full
"entries" span.

### 2. "a matrix" / "a real matrix" point at T, not the definiendum D
- `b64 [form.rel] "a matrix"` has argument term `b67` = **T**.
- `b91` (implicit subject of `b92` "real matrix") links `→b67` = **T**.
But "a (real) matrix" is the **matrix being defined** (the definiendum's subject,
call it D), NOT T. T is the index-set parameter. As annotated it asserts "T is a
matrix", which is false — T is a set of index pairs.
Fix: the matrix predicate's argument (and the implicit subject b91) should
coreference the **matrix input / definiendum D**, not T. (This likely needs D to
exist as an input term to point at.)

## Minor / confirm
- `b58 inputs` = I, J, T (#3). T as an input is defensible (Lean `(T : Set …)`),
  but note T is both an input and the subject of condition `b65 "T ⊆ I × J"`.
  Fine, just confirm intended.
- `b60 name` = "supported on" (T correctly pulled out as an input). Good.
- Multiple separate T-term boxes (b67, b69, b119) — fine, distinct occurrences.
- Coverage 100% throughout; implicit ∧ (b82), → (b103) and coreference edges
  (b91→b67, b101→b97, b114→b97) are all correct mechanisms.

## Verify after fixing
`node tools/inspect.js b14` — subtree should stay 0-issue, and b95 should read
`sym.∀ ∅impl` (implicit) with "entries" as the variable-symbol; b64/b92 arguments
should resolve to D, not T.
