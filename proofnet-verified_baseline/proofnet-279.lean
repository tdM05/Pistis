import Mathlib

open Real
open scoped BigOperators



/-Informal Statement

Prove that $\frac{1}{2}+\frac{1}{3}+\cdots+\frac{1}{n}$ is not an integer.
-/

/-Informal Proof

Let $2^s$ be the largest power of 2 occurring as a denominator in $H_n$, say $2^s=k \leqslant n$. Write $H_n=$ $\frac{1}{2^s}+\left(1+1 / 2+\ldots+1 /(k-1)+1 /(k+1)+\ldots+1 / n\right.$. The sum in parentheses can be written as $1 / 2^{s-1}$ times sum of fractions with odd denominators, so the denominator of the sum in parentheses will not be divisible by $2^s$, but it must equal $2^s$ by Ex $1.29$.
-/

theorem Ireland_Rosen_exercise_1_30 {n : ℕ} :
  ¬ ∃ a : ℤ, ∑ i : Fin n, (1 : ℚ) / (n+2) = a := by
  sorry


/-
The formalized statement above is **false** as it stands.
Reason: when `n = 0` the sum is taken over the empty type `Fin 0`,
so `∑ _ : Fin 0, 1/(0+2) = 0`, which *is* an integer (namely `0`).
The missing premise is that `n` must be positive.
-/

/-
Negation of the original universal claim:
```
¬ (∀ n, ¬ ∃ a : ℤ, ∑ _ : Fin n, (1 : ℚ)/(n+2) = a)
```
We prove it by giving the counterexample `n = 0`.
-/
theorem Ireland_Rosen_exercise_1_30_neg :
  ¬ (∀ n : ℕ, ¬ ∃ a : ℤ, ∑ _ : Fin n, (1 : ℚ) / (n+2) = a) := by
  classical
  -- Step 1: Use `not_forall` to produce a concrete witness for failure of the universal claim.
  refine not_forall.mpr ?_
  -- Step 2: Choose the witness `n = 0` (empty sum is an integer).
  refine ⟨0, ?_⟩
  -- Step 3: It suffices to exhibit an integer value of the sum when `n = 0`.
  intro hneg
  -- Step 4: Provide the explicit witness `a = 0`.
  have hexists : ∃ a : ℤ, ∑ _ : Fin 0, (1 : ℚ) / (0+2) = a := by
    -- Step 4.1: The empty sum is `0`; pair it with the integer `0`.
    refine ⟨0, ?_⟩
    -- Step 4.2: Simplify the sum over `Fin 0`.
    simp
  -- Step 5: Contradict the assumed negation using the constructed witness.
  exact hneg hexists

/-
The original formalization is not faithful to the informal statement.

The informal statement asks to prove that the harmonic-like sum 1/2 + 1/3 + ... + 1/n
is not an integer. The Lean signature instead sums the **constant** 1/(n+2) over Fin n
(the bound variable is anonymous `_`), yielding n * (1/(n+2)) = n/(n+2), which has
nothing to do with the harmonic sum. The denominators 2, 3, ..., n never appear.

The correction replaces the constant summand with a varying one: for each index i in
Finset.range (n-1), the summand is 1/(i+2), producing exactly 1/2 + 1/3 + ... + 1/n.
We also require n ≥ 2 so the sum is non-empty (when n < 2, the sum is 0, an integer).
-/

theorem Ireland_Rosen_exercise_1_30_corrected (n : ℕ) (hn : 2 ≤ n) :
  ¬ ∃ a : ℤ, (Finset.range (n - 1)).sum (fun i => (1 : ℚ) / ((i : ℚ) + 2)) = (a : ℚ) := by
  -- Step 1: establish that our sum equals harmonic(n) - 1.
  -- harmonic n = 1/1 + 1/2 + ... + 1/n, so subtracting 1 gives 1/2 + 1/3 + ... + 1/n.
  have hkey : (Finset.range (n - 1)).sum (fun i => (1 : ℚ) / ((i : ℚ) + 2)) = harmonic n - 1 := by
    -- Step 1.1: rewrite each summand 1/(i+2) as (i+2)⁻¹ for compatibility with harmonic's form.
    have heq : (Finset.range (n - 1)).sum (fun i => (1 : ℚ) / ((i : ℚ) + 2)) =
               (Finset.range (n - 1)).sum (fun i => ((i : ℚ) + 2)⁻¹) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [one_div]
    rw [heq]
    -- Step 1.2: show harmonic n = 1 + ∑ i in range(n-1), (i+2)⁻¹ by splitting off the
    -- first term (i=0, giving (0+1)⁻¹ = 1) from the harmonic sum.
    have hsplit : harmonic n = 1 + (Finset.range (n - 1)).sum (fun i => ((↑i + 2 : ℚ))⁻¹) := by
      -- Step 1.2.1: unfold harmonic to ∑ i in range n, (i+1)⁻¹.
      unfold harmonic
      -- Step 1.2.2: rewrite n as succ(n-1) and apply sum_range_succ' to peel off i=0.
      rw [show n = Nat.succ (n - 1) from by omega]
      rw [Finset.sum_range_succ']
      simp only [zero_add, add_comm]
      congr 1
      -- Step 1.2.3: the peeled-off term (0+1)⁻¹ simplifies to 1.
      · norm_num
      -- Step 1.2.4: show the remaining summands match by reindexing (i+1+1) = (i+2).
      · apply Finset.sum_congr rfl
        intro i _
        congr 1
        push_cast
        ring
    -- Step 1.3: from harmonic n = 1 + our_sum, derive our_sum = harmonic n - 1.
    linarith [hsplit]
  -- Step 2: assume for contradiction that the sum equals some integer a.
  intro ⟨a, ha⟩
  -- Step 3: from our_sum = a and our_sum = harmonic(n) - 1, deduce harmonic n = a + 1.
  have hval : harmonic n = (a + 1 : ℤ) := by
    -- Step 3.1: substitute ha into hkey to get (a : ℚ) = harmonic n - 1.
    have h1 := hkey
    rw [ha] at h1
    -- Step 3.2: use push_cast to unify the integer and rational arithmetic, then solve.
    push_cast at h1 ⊢
    linarith
  -- Step 4: conclude that harmonic n is an integer (its denominator is 1).
  have hint : (harmonic n).isInt = true := by
    -- Step 4.1: rewrite harmonic n as the integer cast ↑(a+1), whose denominator is 1.
    rw [hval]
    simp [Rat.isInt, Rat.den_intCast]
  -- Step 5: apply Mathlib's harmonic_not_int (which states harmonic n is not an integer
  -- for n ≥ 2) to obtain the final contradiction.
  exact harmonic_not_int hn (by rwa [Rat.isInt] at hint)
