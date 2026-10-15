import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators



/-Informal Statement

Suppose $T \in \mathcal{L}(V)$. Prove that if $U_{1}, \ldots, U_{m}$ are subspaces of $V$ invariant under $T$, then $U_{1}+\cdots+U_{m}$ is invariant under $T$.
-/

/-Informal Proof

First off, assume that $U_1, \ldots, U_m$ are subspaces of $V$ invariant under $T$. Now, consider a vector $u \in$ $U_1+\ldots+U_m$. There does exist $u_1 \in U_1, \ldots, u_m \in U_m$ such that $u=u_1+\ldots+u_m$.

Once you apply $T$ towards both sides of the previous equation, we would then get $T u=T u_1+\ldots+$ $T u_m$.

Since each $U_j$ is invariant under $T$, then we would have $T u_1 \in U_1+\ldots+T u_m$. This would then make the equation shows that $T u \in U_1+\ldots+T u_m$, which does imply that $U_1+. .+U_m$ is invariant under $T$
-/

theorem Axler_exercise_5_1 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {T : V →ₗ[F] V} {n : ℕ} (U : Fin n → Submodule F V)
  (hU : ∀ i : Fin n, Submodule.map T (U i) = U i) :
  Submodule.map T (∑ i : Fin n, U i : Submodule F V) =
  (∑ i : Fin n, U i : Submodule F V) := by
  classical
  -- Step 1: Build an induction lemma stating that the image of any finite partial sum equals itself.
  have hgeneral :
      ∀ s : Finset (Fin n),
        Submodule.map T (∑ i ∈ s, U i) = ∑ i ∈ s, U i := by
    -- Step 1.1: Perform induction on the finite set `s`.
    intro s
    refine Finset.induction_on s ?base ?step
    · -- Step 1.1.1: Base case `s = ∅`, where the sum is `⊥`, whose image is still `⊥`.
      -- Step 1.1.1.1: `simp` uses `Submodule.map_bot` to close the goal immediately.
      simp
    · -- Step 1.1.2: Inductive step—insert a fresh index `a` into a set `s`.
      intro a s ha h_ind
      -- Step 1.1.2.1: Expand the sum over `insert a s` and rewrite addition as a supremum.
      -- Step 1.1.2.2: Apply `Submodule.map_sup`, the inductive hypothesis, and invariance `hU`.
      simp [Finset.sum_insert, ha, Submodule.add_eq_sup, Submodule.map_sup, h_ind, hU a]
  -- Step 2: Specialize the helper lemma to the complete index set `Finset.univ`.
  -- Step 2.1: The stated sum `∑ i : Fin n, U i` is precisely the sum over `Finset.univ`.
  simpa using hgeneral Finset.univ


/-
Faithfulness Correction:

The original formalization uses `Submodule.map T (U i) = U i` (equality), meaning
T(U_i) = U_i, i.e., each U_i is *fixed* by T (T maps U_i onto itself bijectively).
However, the informal statement only requires that each U_i is *invariant* under T,
which means T(U_i) ⊆ U_i — every element of U_i is mapped into U_i, but T need not
be surjective onto U_i.

Similarly, the conclusion should be containment `T(U_1 + ... + U_m) ⊆ U_1 + ... + U_m`
(invariance), not equality `T(U_1 + ... + U_m) = U_1 + ... + U_m` (fixed).

The corrected version below uses `≤` (which is `⊆` for submodules) in both the
hypothesis and the conclusion, faithfully encoding "invariant under T."
-/

theorem Axler_exercise_5_1_corrected {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {T : V →ₗ[F] V} {n : ℕ} (U : Fin n → Submodule F V)
  (hU : ∀ i : Fin n, Submodule.map T (U i) ≤ U i) :
  Submodule.map T (∑ i : Fin n, U i : Submodule F V) ≤
  (∑ i : Fin n, U i : Submodule F V) := by
  classical
  -- Step 1: Prove a generalized lemma for any finite subset of indices.
  -- This lets us use Finset induction rather than dealing with Fin n directly.
  have hgeneral :
      ∀ s : Finset (Fin n),
        Submodule.map T (∑ i ∈ s, U i) ≤ ∑ i ∈ s, U i := by
    -- Step 1.1: Introduce the arbitrary finite set s.
    intro s
    -- Step 1.2: Perform induction on s using Finset.induction_on.
    refine Finset.induction_on s ?base ?step
    · -- Step 1.2.1: Base case — s = ∅.
      -- The sum over the empty set is ⊥ (the trivial submodule).
      -- Submodule.map T ⊥ = ⊥ ≤ ⊥, which simp discharges via Submodule.map_bot.
      simp
    · -- Step 1.2.2: Inductive step — insert a fresh index `a` into set `s`.
      -- We have:
      --   ha : a ∉ s
      --   h_ind : Submodule.map T (∑ i ∈ s, U i) ≤ ∑ i ∈ s, U i
      intro a s ha h_ind
      -- Step 1.2.2.1: Rewrite the sum over `insert a s` as `U a + ∑ i ∈ s, U i`,
      -- then convert submodule addition to lattice supremum (`+` = `⊔` for submodules),
      -- then distribute `map T` over the supremum via `Submodule.map_sup`.
      -- After these rewrites the goal becomes:
      --   Submodule.map T (U a) ⊔ Submodule.map T (∑ i ∈ s, U i) ≤ U a ⊔ ∑ i ∈ s, U i
      simp only [Finset.sum_insert ha, Submodule.add_eq_sup, Submodule.map_sup]
      -- Step 1.2.2.2: Apply `sup_le_sup` which states: if a ≤ b and c ≤ d, then a ⊔ c ≤ b ⊔ d.
      -- The two hypotheses are:
      --   hU a   : Submodule.map T (U a) ≤ U a          (invariance of U a)
      --   h_ind  : Submodule.map T (∑ i ∈ s, U i) ≤ ∑ i ∈ s, U i  (induction hypothesis)
      exact sup_le_sup (hU a) h_ind
  -- Step 2: Specialize the general lemma to the complete index set Finset.univ.
  -- The unqualified sum `∑ i : Fin n, U i` is definitionally `∑ i ∈ Finset.univ, U i`,
  -- so `simpa` handles the conversion and closes the goal.
  simpa using hgeneral Finset.univ
