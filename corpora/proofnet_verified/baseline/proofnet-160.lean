import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

noncomputable def g (n : ℕ) : ℝ := Real.sqrt (n + 1) - Real.sqrt n

/-Informal Statement

Prove that $\lim_{n \rightarrow \infty} \sum_{i < n} a_i = \infty$, where $a_i = \sqrt{i + 1} -\sqrt{i}$.
-/

/-Informal Proof

(a) Multiplying and dividing $a_n$ by $\sqrt{n+1}+\sqrt{n}$, we find that $a_n=\frac{1}{\sqrt{n+1}+\sqrt{n}}$, which is larger than $\frac{1}{2 \sqrt{n+1}}$. The series $\sum a_n$ therefore diverges by comparison with the $p$ series $\left(p=\frac{1}{2}\right)$.
-/

theorem Rudin_exercise_3_6a
: Tendsto (λ (n : ℕ) => (∑ i ∈ range n, g i)) atTop atTop := by
  -- Step 1: Establish a closed-form expression for the partial sums via induction.
  have htel : ∀ n : ℕ, (∑ i ∈ range n, g i) = Real.sqrt n := by
    -- Step 1.1: Prove the identity by induction on `n`.
    refine Nat.rec ?base ?step
    · -- Step 1.1.1: Base case `n = 0`, both sides are zero.
      simp [g]
    · -- Step 1.1.2: Inductive step from `n` to `n + 1`.
      intro n hn
      -- Step 1.1.2.1: Expand the `(n + 1)`-st partial sum to isolate the new term.
      have hdecomp :
          (∑ i ∈ range (Nat.succ n), g i)
            = (∑ i ∈ range n, g i) + g n := by
        simpa using (Finset.sum_range_succ (fun i => g i) n)
      -- Step 1.1.2.2: Substitute the inductive hypothesis and unwind the algebraic expression.
      calc
        (∑ i ∈ range (Nat.succ n), g i)
            = (∑ i ∈ range n, g i) + g n := hdecomp
        _ = Real.sqrt n + g n := by
          simp [hn]
        _ = Real.sqrt (n + 1) := by
          simp [g, sub_eq_add_neg, add_comm]
        -- Step 1.1.2.3: Align notations so that the rewritten expression matches the goal.
        _ = Real.sqrt (Nat.succ n) := by
          simp [Nat.succ_eq_add_one]
  -- Step 2: Show that `sqrt n` diverges to `+∞` as `n → ∞`.
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop := by
    -- Step 2.1: Use the `atTop` characterization via eventual lower bounds.
    refine tendsto_atTop.2 ?_
    -- Step 2.2: Fix an arbitrary real bound `b` and find where the sequence stays above it.
    intro b
    -- Step 2.3: Reduce to an eventual statement on natural numbers.
    refine eventually_atTop.2 ?_
    -- Step 2.4: Choose a natural `N` forcing `(max b 0)^2 ≤ N`.
    obtain ⟨N, hN⟩ := exists_nat_ge ((max b 0) ^ 2)
    refine ⟨N, ?_⟩
    -- Step 2.5: Prove the desired inequality for every `n ≥ N`.
    intro n hn
    -- Step 2.5.1: Transfer the bound on squares to `(n : ℝ)`.
    have hsq : (max b 0) ^ 2 ≤ (n : ℝ) := by
      have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact hN.trans this
    -- Step 2.5.2: Convert the square inequality to a statement about square roots.
    have hmax : max b 0 ≤ Real.sqrt n := Real.le_sqrt_of_sq_le hsq
    -- Step 2.5.3: Use `b ≤ max b 0` to finish the bound `b ≤ sqrt n`.
    exact (le_max_left _ _).trans hmax
  -- Step 3: Translate the telescoping identity into a pointwise equality of functions.
  have hfun :
      (fun n : ℕ => ∑ i ∈ range n, g i) = fun n : ℕ => Real.sqrt n := by
    -- Step 3.1: Apply `funext` to reuse the closed-form expression.
    funext n
    exact htel n
  -- Step 4: Rewrite the target limit using the previously proven equality.
  simpa [hfun] using hsqrt
