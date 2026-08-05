import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Prove that the center of the product of two groups is the product of their centers.
-/

/-Informal Proof

We have that $(g_1, g_2)\cdot (h_1, h_2) = (h_1, h_2)\cdot (g_1, g_2)$ if and only if $g_1h_1 = h_1g_1$ and $g_2h_2 = h_2g_2$.
-/

theorem Artin_exercise_2_8_6 {G H : Type*} [Group G] [Group H] :
  Nonempty (center (G × H) ≃* (center G) × (center H)) := by
  classical
  -- Step 1: Define the forward map by projecting a central pair to its two central components.
  let toProd : center (G × H) → (center G) × (center H) :=
    fun z =>
      (⟨z.1.1, by
          -- Step 1.1: show the first component commutes with every element of `G`.
          refine Subgroup.mem_center_iff.mpr ?_
          intro g
          -- Step 1.1.1: evaluate the centrality condition at `(g, 1)` in `G × H`.
          have hx :=
            congrArg Prod.fst ((Subgroup.mem_center_iff.mp z.2) ⟨g, (1 : H)⟩)
          -- Step 1.1.2: extract the equality in `G` from that pairwise equality.
          simpa using hx⟩,
        ⟨z.1.2, by
          -- Step 1.2: show the second component commutes with every element of `H`.
          refine Subgroup.mem_center_iff.mpr ?_
          intro h
          -- Step 1.2.1: evaluate the centrality condition at `(1, h)` in `G × H`.
          have hy :=
            congrArg Prod.snd ((Subgroup.mem_center_iff.mp z.2) ⟨(1 : G), h⟩)
          -- Step 1.2.2: extract the equality in `H` from that pairwise equality.
          simpa using hy⟩)
  -- Step 2: Define the inverse map by pairing two central elements into a central element of the product.
  let invProd : (center G) × (center H) → center (G × H) :=
    fun z =>
      ⟨⟨z.1.1, z.2.1⟩, by
        -- Step 2.1: prove that the constructed pair commutes with any `(g, h)` in `G × H`.
        refine Subgroup.mem_center_iff.mpr ?_
        intro x
        rcases x with ⟨g, h⟩
        -- Step 2.1.1: use componentwise equalities stemming from centrality in `G` and `H`.
        apply Prod.ext
        · -- Step 2.1.1.1: first coordinate follows from centrality in `G`.
          dsimp
          simpa using (Subgroup.mem_center_iff.mp z.1.2 g)
        · -- Step 2.1.1.2: second coordinate follows from centrality in `H`.
          dsimp
          simpa using (Subgroup.mem_center_iff.mp z.2.2 h)⟩
  -- Step 3: Assemble the maps into a multiplicative equivalence between the two centers.
  refine ⟨
    ⟨⟨toProd, invProd, ?_, ?_⟩, ?_⟩⟩
  -- Step 3.1: prove that `toProd` followed by `invProd` is the identity on `center (G × H)`.
  · intro z
    -- Step 3.1.1: equality of subtypes reduces to equality of the underlying pairs.
    ext <;> simp [toProd, invProd]
  -- Step 3.2: prove that `invProd` followed by `toProd` is the identity on `(center G) × (center H)`.
  · intro z
    -- Step 3.2.1: again, reduce to equality componentwise.
    ext <;> simp [toProd, invProd]
  -- Step 3.3: verify that `toProd` preserves multiplication.
  · intro x y
    -- Step 3.3.1: compare images componentwise; each side simplifies by definition.
    ext <;> simp [toProd]


/-
## Faithfulness Issue

The original formalization above uses:

    Nonempty (center (G × H) ≃* (center G) × (center H))

This asserts only the existence of *some* abstract group isomorphism between
`center (G × H)` and `(center G) × (center H)`. However, the informal statement
says "the center of the product **is** the product of their centers," which is a
subgroup equality — not merely an abstract isomorphism.

The distinction matters: two subgroups of `G × H` can be abstractly isomorphic as
groups without being the same subgroup (the `MulEquiv` need not respect the
embeddings into `G × H`). So the Lean statement is strictly weaker than the
informal claim.

## Corrected Formalization

The faithful formalization uses `Subgroup.prod` to express the product of
subgroups as a subgroup of `G × H`, then asserts equality:

    Subgroup.center (G × H) = (Subgroup.center G).prod (Subgroup.center H)

This is exactly what Mathlib's `Set.center_prod` states at the set level.
-/

theorem Artin_exercise_2_8_6_corrected {G H : Type*} [Group G] [Group H] :
    Subgroup.center (G × H) = (Subgroup.center G).prod (Subgroup.center H) := by
  -- Step 1: reduce subgroup equality to pointwise membership equivalence via extensionality.
  ext ⟨g, h⟩
  -- Step 1.1: simplify both sides using the definitions of `mem_center_iff`, `mem_prod`,
  -- `Prod.forall`, and `Prod.ext_iff` so the goal becomes:
  -- `(∀ a b, g * a = a * g ∧ h * b = b * h) ↔ (∀ a, g * a = a * g) ∧ (∀ b, h * b = b * h)`
  simp [Subgroup.mem_center_iff, Subgroup.mem_prod, Prod.forall, Prod.ext_iff]
  -- Step 2: prove the biconditional by splitting into forward and backward directions.
  constructor
  -- Step 2.1 (forward): assume `(g, h)` is central in `G × H`, i.e.,
  -- `∀ a b, g * a = a * g ∧ h * b = b * h`. Show `g` is central in `G` and `h` is central in `H`.
  · intro hx
    -- Step 2.1.1: for centrality of `g`, specialize at `(a, 1)` and take the first component.
    -- Step 2.1.2: for centrality of `h`, specialize at `(1, b)` and take the second component.
    exact ⟨fun a => (hx a 1).1, fun b => (hx 1 b).2⟩
  -- Step 2.2 (backward): assume `g` is central in `G` and `h` is central in `H`.
  -- Show `(g, h)` commutes with every `(a, b)` in `G × H` componentwise.
  · intro ⟨hg, hh⟩ a b
    -- Step 2.2.1: the first component `g * a = a * g` follows from `hg a`.
    -- Step 2.2.2: the second component `h * b = b * h` follows from `hh b`.
    exact ⟨hg a, hh b⟩
