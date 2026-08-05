import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $\sigma, \tau$ are two permutations that disturb no common element and $\sigma \tau = e$, prove that $\sigma = \tau = e$.
-/

/-Informal Proof

Note that $\sigma \tau=e$ can equivalentnly be phrased as $\tau$ being the inverse of $\sigma$. Our statement is then equivalent to the statement that an inverse of a nonidentity permutation disturbs at least one same element as that permutation. To prove this, let $\sigma$ be a nonidentity permutation, then let $\left(i_1 \cdots i_n\right)$ be a cycle in $\sigma$. Then we have that
$$
\sigma\left(i_1\right)=i_2, \sigma\left(i_2\right)=i_2, \ldots, \sigma\left(i_{n-1}\right)=i_n, \sigma\left(i_n\right)=i_1,
$$
but then also
$$
i_1=\tau\left(i_2\right), i_2=\tau\left(i_3\right), \ldots, i_{n-1}=\tau\left(i_n\right), i_n=\tau\left(i_1\right),
$$
i.e. its inverse disturbs $i_1, \ldots, i_n$.
-/


theorem Herstein_exercise_3_2_21 {α : Type*} [Fintype α] {σ τ: Equiv.Perm α}
  (h1 : ∀ a : α, σ a = a ↔ τ a ≠ a) (h2 : τ ∘ σ = id) :
  σ = 1 ∧ τ = 1 := by
  classical
  -- Step 1: show σ fixes every element of α via contradiction on an arbitrary a.
  have hσfix : ∀ a : α, σ a = a := by
    intro a
    -- Step 1.1: suppose σ moves a and derive contradictory information about τ.
    by_contra hne
    -- Step 1.2: translate the equivalence h1 at a to conclude τ fixes a.
    have hτfix : τ a = a := by
      have hnot : ¬ τ a ≠ a := (not_congr (h1 a)).mp hne
      exact not_not.mp hnot
    -- Step 1.3: evaluate τ ∘ σ at a and use injectivity of τ to contradict hne.
    have hcomp := congrArg (fun f : α → α => f a) h2
    have hcomp' : τ (σ a) = a := by
      simpa [Function.comp] using hcomp
    have : σ a = a := by
      apply τ.injective
      calc
        τ (σ a) = a := hcomp'
        _ = τ a := by simpa using hτfix.symm
    exact hne this
  -- Step 2: convert the pointwise fixing result into σ = 1.
  have hσ : σ = 1 := by
    ext a
    -- Step 2.1: apply the pointwise equality at each a.
    simpa using hσfix a
  -- Step 3: use h2 together with hσfix to show τ fixes every element.
  have hτfix : ∀ a : α, τ a = a := by
    intro a
    -- Step 3.1: evaluate τ ∘ σ on a and simplify with Step 1 result.
    have hcomp := congrArg (fun f : α → α => f a) h2
    simpa [Function.comp, hσfix a] using hcomp
  -- Step 4: convert the pointwise fixing of τ into τ = 1 and conclude.
  have hτ : τ = 1 := by
    ext a
    -- Step 4.1: apply the pointwise equality for τ.
    simpa using hτfix a
  -- Step 5: package the two equalities into the desired conjunction.
  exact ⟨hσ, hτ⟩


/-
## Faithfulness Issues

The original formalization has two problems:

1. The hypothesis `∀ a : α, σ a = a ↔ τ a ≠ a` is strictly stronger than what the
   informal statement requires. The informal says "σ and τ disturb no common element,"
   meaning ∀ a, ¬(σ a ≠ a ∧ τ a ≠ a) — no element is moved by both. The biconditional
   additionally forces every element to be moved by exactly one of σ or τ (they cannot
   both fix an element), which the informal does not require.

2. The `[Fintype α]` hypothesis is unnecessary. The informal statement says "two
   permutations" without restricting to finite sets, and the proof does not use finiteness
   at all: from στ = e we get τ = σ⁻¹, and if σ moves x then σ⁻¹ also moves x
   (since σ⁻¹(x) = x would imply x = σ(x)), so τ moves x too, contradicting h1.
   Adding an unneeded hypothesis narrows the scope and makes the statement weaker.

## Corrected Formalization

The correction:
- Replaces `↔` with `¬(... ∧ ...)` to faithfully capture "disturb no common element."
- Removes `[Fintype α]` since finiteness is not needed.
- Uses `τ * σ = 1` (group multiplication in `Equiv.Perm α`) instead of `τ ∘ σ = id`.
-/

theorem Herstein_exercise_3_2_21_corrected {α : Type*} {σ τ : Equiv.Perm α}
  (h1 : ∀ a : α, ¬(σ a ≠ a ∧ τ a ≠ a)) (h2 : τ * σ = 1) :
  σ = 1 ∧ τ = 1 := by
  -- Step 1: from τ * σ = 1, derive τ = σ⁻¹.
  have hτ_eq : τ = σ⁻¹ := by
    have := congr_arg (· * σ⁻¹) h2
    simpa using this
  -- Step 2: show σ = 1 by proving σ fixes every element via contradiction.
  have hσ : σ = 1 := by
    ext a
    -- Step 2.1: reduce the goal to showing σ a = a.
    simp only [Equiv.Perm.one_apply]
    -- Step 2.2: assume for contradiction that σ moves a, i.e., σ a ≠ a.
    by_contra hne
    -- Step 2.3: since τ = σ⁻¹, show that τ also moves a.
    -- (If σ⁻¹(a) = a, then applying σ to both sides gives a = σ(a), contradicting hne.)
    have hτ_moves : τ a ≠ a := by
      rw [hτ_eq]
      simp only [Equiv.Perm.inv_def]
      -- Step 2.3.1: assume for contradiction that σ.symm a = a.
      intro heq
      -- Step 2.3.2: apply σ to both sides: σ(σ.symm(a)) = σ(a), so a = σ(a).
      have : σ (σ.symm a) = σ a := by rw [heq]
      -- Step 2.3.3: simplify σ(σ.symm(a)) = a on the left, yielding a = σ(a).
      simp at this
      -- Step 2.3.4: this gives σ(a) = a, contradicting our assumption hne.
      exact hne this.symm
    -- Step 2.4: from h1, σ and τ cannot both move a — but we just showed both do.
    exact h1 a ⟨hne, hτ_moves⟩
  -- Step 3: derive τ = 1 from τ = σ⁻¹ and σ = 1.
  have hτ : τ = 1 := by
    -- Step 3.1: substitute σ = 1 into τ = σ⁻¹ to get τ = 1⁻¹ = 1.
    rw [hτ_eq, hσ, inv_one]
  -- Step 4: package both results into the conjunction σ = 1 ∧ τ = 1.
  exact ⟨hσ, hτ⟩
