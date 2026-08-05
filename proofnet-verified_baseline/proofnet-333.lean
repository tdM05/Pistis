import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Let $E$ be a nonempty subset of a total ordered set; suppose $\alpha$ is a lower bound of $E$ and $\beta$ is an upper bound of $E$. Prove that $\alpha \leq \beta$.
-/

/-Informal Proof

Since $E$ is nonempty, there exists $x \in E$. Then by definition of lower and upper bounds we have $\alpha \leq x \leq \beta$, and hence by property $i i$ in the definition of an ordering, we have $\alpha<\beta$ unless $\alpha=x=\beta$.
-/

theorem Rudin_exercise_1_4
(α : Type*) [PartialOrder α]
(s : Set α)
(x y : α)
(h₀ : Set.Nonempty s)
(h₁ : x ∈ lowerBounds s)
(h₂ : y ∈ upperBounds s)
: x ≤ y := by
  -- Step 1: Extract a specific element `z` from the assumption that `s` is nonempty.
  obtain ⟨z, hz⟩ := h₀
  -- Step 2: Prove that `x ≤ z` by applying the fact that `x` is a lower bound of `s`.
  have hxz : x ≤ z := by
    -- Step 2.1: The definition of `x ∈ lowerBounds s` gives `x ≤ a` for every `a ∈ s`,
    -- so we specialize it to the particular witness `z`.
    exact h₁ hz
  -- Step 3: Prove that `z ≤ y` by using that `y` is an upper bound of `s`.
  have hzy : z ≤ y := by
    -- Step 3.1: From the definition of `y ∈ upperBounds s`, every element of `s` (in particular `z`)
    -- lies below `y`, so we again specialize the defining property to `z`.
    exact h₂ hz
  -- Step 4: Chain the inequalities `x ≤ z` and `z ≤ y` to reach the desired inequality `x ≤ y`.
  -- Step 4.1: Use transitivity of `≤` in the partial order to combine the two inequalities.
  exact hxz.trans hzy


/-
## Why the Original Formalization is Not Faithful

The informal statement (Rudin's definition) refers to an "ordered set", which in Rudin's
terminology means a **linearly (totally) ordered set**. The Lean formalization uses
`[PartialOrder α]`, which is strictly weaker — it only requires reflexivity, antisymmetry,
and transitivity, without the totality axiom (∀ a b, a ≤ b ∨ b ≤ a).

Since every linear order is a partial order, the Lean theorem is **logically stronger** than
the informal claim: it proves the same conclusion under a weaker hypothesis. The proof itself
only uses transitivity and never invokes totality, so the result holds in both settings.
Nevertheless, the formalization does not faithfully capture the intended hypothesis.

## Correction

Replace `[PartialOrder α]` with `[LinearOrder α]` to match Rudin's "ordered set".
The proof is identical since totality is not needed.
-/

theorem Rudin_exercise_1_4_corrected
(α : Type*) [LinearOrder α]
(s : Set α)
(x y : α)
(h₀ : Set.Nonempty s)
(h₁ : x ∈ lowerBounds s)
(h₂ : y ∈ upperBounds s)
: x ≤ y := by
  -- Step 1: Extract a specific element `z` from the assumption that `s` is nonempty.
  obtain ⟨z, hz⟩ := h₀
  -- Step 2: Chain `x ≤ z` (lower bound) and `z ≤ y` (upper bound) by transitivity.
  exact (h₁ hz).trans (h₂ hz)
