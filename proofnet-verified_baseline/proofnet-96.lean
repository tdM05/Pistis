import Mathlib

open Real
open scoped BigOperators
open scoped ArithmeticFunction ArithmeticFunction.Moebius



/-Informal Statement

Define $\wedge(n)=\log p$ if $n$ is a power of $p$ and zero otherwise. Prove that $\sum_{A \mid n} \mu(n / d) \log d$ $=\wedge(n)$.
-/

/-Informal Proof

$$
\left\{
\begin{array}{cccl}
    \land(n)& =  & \log p & \mathrm{if}\  n =p^\alpha,\ \alpha \in \mathbb{N}^*  \\
  &  = &   0 & \mathrm{otherwise }.
\end{array}
\right.
$$
Let $n = p_1^{\alpha_1}\cdots p_t^{\alpha_t}$ the decomposition of $n$ in prime factors. As $\land(d) = 0$ for all divisors of $n$, except for $d = p_j^i, i>0, j=1,\ldots t$,
\begin{align*}
\sum_{d \mid n} \land(d)&= \sum_{i=1}^{\alpha_1} \land(p_1^{i}) + \cdots+ \sum_{i=1}^{\alpha_t} \land(p_t^{i})\\ 
&= \alpha_1 \log p_1+\cdots + \alpha_t \log p_t\\
&= \log n
\end{align*}
By Mobius Inversion Theorem,
$$\land(n) = \sum_{d \mid n} \mu\left (\frac{n}{d}\right ) \log d.$$
-/

theorem Ireland_Rosen_exercise_2_21 {l : ℕ → ℝ}
  (hl : ∀ p n : ℕ, p.Prime → l (p^n) = log p )
  (hl1 : ∀ m : ℕ, ¬ IsPrimePow m → l m = 0) :
  l = λ n => ∑ d : Nat.divisors n, ArithmeticFunction.moebius (n/d) * log d  := by
  sorry

/-
Step 0: The displayed formal hypotheses force `l 1 = Real.log 2` from `hl` (take `p = 2`, `n = 0`)
while simultaneously requiring `l 1 = 0` from `hl1` (because `1` is not a prime power). Hence no
function can satisfy both assumptions, so the original Lean statement cannot capture the intended
claim.
-/

theorem Ireland_Rosen_exercise_2_21_neg :
  ¬ ∃ l : ℕ → ℝ,
      (∀ p n : ℕ, p.Prime → l (p ^ n) = log p) ∧
      (∀ m : ℕ, ¬ IsPrimePow m → l m = 0) := by
  -- Step 1: Assume, for contradiction, that such a function `l` exists.
  rintro ⟨l, hl, hl1⟩
  -- Step 2: Specialise `hl` at the prime `2` and exponent `0` to obtain `l 1 = log 2`.
  have h_log_two : l 1 = log (2 : ℝ) := by
    -- Step 2.1: Here we rewrite `2 ^ 0` to `1` so that the left-hand side becomes `l 1`.
    simpa [pow_zero] using hl 2 0 Nat.prime_two
  -- Step 3: Apply `hl1` to `m = 1` to deduce `l 1 = 0`, because `1` is not a prime power.
  have h_zero : l 1 = 0 := by
    -- Step 3.1: The lemma `not_isPrimePow_one` supplies the required negation hypothesis.
    simpa using hl1 1 not_isPrimePow_one
  -- Step 4: Combine the previous two equalities to get the contradictory equation `0 = log 2`.
  have h_contra_eq : (0 : ℝ) = log (2 : ℝ) := by simpa [h_zero] using h_log_two
  -- Step 5: Use the positivity of `log 2` to refute `0 = log 2`.
  have h_log_pos : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  -- Step 5.1: Substituting the contradictory equality into the positivity statement yields `0 < 0`.
  have : (0 : ℝ) < 0 := by simp [h_contra_eq] at h_log_pos
  -- Step 5.2: The inequality `0 < 0` is impossible, concluding the contradiction.
  exact (lt_irrefl (0 : ℝ)) this

/-
Step 0: Corrected formulation.
To align with the informal von Mangoldt identity, require the exponent in `l (p^n)` to satisfy
`0 < n`, ensuring the only forced value at `1` is `l 1 = 0`. Under these consistent hypotheses the
resulting function must equal the Dirichlet convolution `log * μ`, which mathlib identifies with
the von Mangoldt function Λ.
-/

theorem Ireland_Rosen_exercise_2_21_corrected {l : ℕ → ℝ}
  (hl : ∀ p n : ℕ, p.Prime → 0 < n → l (p ^ n) = Real.log p)
  (hl1 : ∀ m : ℕ, ¬ IsPrimePow m → l m = 0) :
  l = fun n ↦ (∑ d ∈ Nat.divisors n, ((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) * log d) := by
  -- Step 1: Reduce the goal to pointwise equality of functions.
  funext n
  -- Step 1.1: Enable classical logic for destructive reasoning about `IsPrimePow`.
  classical
  -- Step 2: Show `l n` equals the von Mangoldt function Λ evaluated at `n`.
  have h_l_eq_vonMangoldt : l n = ArithmeticFunction.vonMangoldt n := by
    -- Step 2.1: Split into the cases where `n` is or is not a prime power.
    by_cases hn : IsPrimePow n
    · -- Step 2.1.1: Handle the prime power case by extracting the prime `p` and exponent `k > 0`.
      obtain ⟨p, k, hp, hk_pos, rfl⟩ := (isPrimePow_nat_iff _).1 hn
      -- Step 2.1.1.1: Convert the positivity witness into the non-zero exponent needed below.
      have hk_ne_zero : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk_pos
      -- Step 2.1.1.2: Evaluate `l` on `p ^ k` via the corrected hypothesis `hl`.
      have h_l_value : l (p ^ k) = log (p : ℝ) := hl p k hp hk_pos
      -- Step 2.1.1.3: Evaluate Λ on the same prime power using the dedicated mathlib lemma.
      have h_von_value :
          ArithmeticFunction.vonMangoldt (p ^ k) = log (p : ℝ) := by
        -- Step 2.1.1.3.1: Λ is constant along positive powers, reducing to the prime case.
        have h_pow := ArithmeticFunction.vonMangoldt_apply_pow (n := p) (k := k) hk_ne_zero
        -- Step 2.1.1.3.2: Evaluate Λ at the prime `p`.
        have h_prime := ArithmeticFunction.vonMangoldt_apply_prime hp
        -- Step 2.1.1.3.3: Chain the two results to obtain the desired value for `p ^ k`.
        exact h_pow.trans h_prime
      -- Step 2.1.1.4: Conclude that `l` and Λ agree in the prime power case.
      simpa [h_von_value]
    · -- Step 2.1.2: When `n` is not a prime power, both functions vanish.
      have h_l_zero : l n = 0 := hl1 n hn
      have h_von_zero : ArithmeticFunction.vonMangoldt n = 0 :=
        (ArithmeticFunction.vonMangoldt_eq_zero_iff).2 hn
      -- Step 2.1.2.1: Substitute the vanishing of Λ to complete the equality.
      simpa [h_von_zero] using h_l_zero
  -- Step 3: Rewrite the divisor sum as Λ via the convolution identity `log * μ = Λ`.
  have h_sum_eq_vonMangoldt :
      ∑ d ∈ Nat.divisors n, ((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) * log d =
        ArithmeticFunction.vonMangoldt n := by
    -- Step 3.1: Evaluate the arithmetic-function equality pointwise at `n`.
    have h_convolution :
        ((ArithmeticFunction.log : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)) n =
          ArithmeticFunction.vonMangoldt n :=
      congrArg (fun f : ArithmeticFunction ℝ => f n)
        ArithmeticFunction.log_mul_moebius_eq_vonMangoldt
    -- Step 3.2: Expand the Dirichlet convolution into a single divisor sum.
    have h_explicit :
        ((ArithmeticFunction.log : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)) n =
          ∑ d ∈ Nat.divisors n, ((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) * log d := by
      -- Step 3.2.1: Write the convolution as a sum over the divisor antidiagonal.
      have h_antidiagonal_base :=
        (ArithmeticFunction.mul_apply (f := (ArithmeticFunction.log : ArithmeticFunction ℝ))
          (g := (μ : ArithmeticFunction ℝ)) (n := n))
      have h_antidiagonal :
          ((ArithmeticFunction.log : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)) n =
            ∑ x ∈ Nat.divisorsAntidiagonal n,
              log (x.1 : ℝ) * ((ArithmeticFunction.moebius x.2 : ℤ) : ℝ) := by
        simpa [ArithmeticFunction.log_apply] using h_antidiagonal_base
      -- Step 3.2.2: Reindex the antidiagonal sum to a standard divisor sum.
      have h_reindex :
          (∑ x ∈ Nat.divisorsAntidiagonal n,
              log (x.1 : ℝ) * ((ArithmeticFunction.moebius x.2 : ℤ) : ℝ)) =
            ∑ d ∈ Nat.divisors n,
              ((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) * log (d : ℝ) := by
        simpa [mul_comm] using
          (Nat.sum_divisorsAntidiagonal fun i j =>
            log (i : ℝ) * ((ArithmeticFunction.moebius j : ℤ) : ℝ))
      -- Step 3.2.3: Combine the two equalities to obtain the desired explicit formula.
      exact h_antidiagonal.trans h_reindex
    -- Step 3.3: Combine the explicit formula with the known convolution identity.
    exact h_explicit.symm.trans h_convolution
  -- Step 4: Combine the two identifications to reach the target equality.
  exact h_l_eq_vonMangoldt.trans h_sum_eq_vonMangoldt.symm
