import Mathlib

open Real
open scoped BigOperators



/-Informal Statement

For all odd $n$ show that $8 \mid n^{2}-1$.
-/

/-Informal Proof

We have $n^2-1=(n+1)(n-1)$. Since $n$ is odd, both $n+1, n-1$ are even, and moreso, one of these must be divisible by 4 , as one of the two consecutive odd numbers is divisible by 4 . Thus, their product is divisible by 8 . Similarly, if 3 does not divide $n$, it must divide one of $n-1, n+1$, otherwise it wouldn't divide three consecutive integers, which is impossible. As $n$ is odd, $n+1$ is even, so $(n+1)(n-1)$ is divisible by both 2 and 3 , so it is divisible by 6 .
-/

theorem Ireland_Rosen_exercise_1_27 {n : ℕ} (hn : Odd n) : 8 ∣ (n^2 - 1) := by
  -- Step 1: Extract the witness that certifies n is odd, so that n = 2 * k + 1.
  obtain ⟨k, hk⟩ := hn
  -- Step 2: Rewrite n^2 - 1 using the representation n = 2 * k + 1.
  have hcalc : n^2 - 1 = 4 * k * (k + 1) := by
    -- Step 2.1: Substitute the expression for n coming from oddness.
    -- Step 2.2: Expand the square and reorganize terms to expose the factor 4 * k * (k + 1).
    have hsq : (2 * k + 1)^2 = 4 * k^2 + 4 * k + 1 := by
      -- Step 2.2.1: Expand (2 * k + 1)^2 into a polynomial in k.
      ring
    have hsub : (2 * k + 1)^2 - 1 = 4 * k^2 + 4 * k := by
      -- Step 2.2.2: Remove the final "+ 1" using the matching subtraction.
      calc
        (2 * k + 1)^2 - 1 = (4 * k^2 + 4 * k + 1) - 1 := by simp [hsq]
        _ = ((4 * k^2 + 4 * k) + 1) - 1 := by
              simp [add_comm]
        _ = 4 * k^2 + 4 * k := by
              simp
    have hfactor : 4 * k^2 + 4 * k = 4 * k * (k + 1) := by
      -- Step 2.2.3: Factor out the shared 4 and the linear term k.
      calc
        4 * k^2 + 4 * k = 4 * (k^2 + k) := by ring
        _ = 4 * k * (k + 1) := by ring
    -- Step 2.3: Combine the intermediate equalities to obtain the desired factorization.
    calc
      n^2 - 1 = (2 * k + 1)^2 - 1 := by simp [hk]
      _ = 4 * k^2 + 4 * k := hsub
      _ = 4 * k * (k + 1) := hfactor
  -- Step 3: Show that 8 divides the product 4 * k * (k + 1).
  have hdiv : 8 ∣ 4 * k * (k + 1) := by
    -- Step 3.1: Split on whether k is even or odd.
    obtain hkeven | hkodd := k.even_or_odd
    · -- Step 3.2: Treat the case where k is even.
      rcases hkeven with ⟨t, ht⟩
      -- Step 3.2.0: Rewrite the evenness witness into the more convenient form k = 2 * t.
      have ht2 : k = 2 * t := by
        -- Step 3.2.0.1: Replace the double addition by a multiplication by 2.
        simpa [two_mul, add_comm, add_left_comm] using ht
      -- Step 3.2.1: Produce the required witness for divisibility in the even case.
      refine ⟨t * (2 * t + 1), ?_⟩
      -- Step 3.2.2: Simplify the expression to factor out the 8 explicitly.
      calc
        4 * k * (k + 1)
            = 4 * (2 * t) * ((2 * t) + 1) := by simp [ht2]
        _ = 8 * t * ((2 * t) + 1) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
        _ = 8 * (t * (2 * t + 1)) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
    · -- Step 3.3: Treat the case where k is odd.
      rcases hkodd with ⟨t, ht⟩
      -- Step 3.3.0: Rewrite the oddness witness into the form k = 2 * t + 1.
      have ht2 : k = 2 * t + 1 := by
        -- Step 3.3.0.1: Convert the double addition into a multiplication by 2.
        simpa [two_mul, add_comm, add_left_comm, add_assoc] using ht
      -- Step 3.3.1: Produce the required witness for divisibility in the odd case.
      refine ⟨(2 * t + 1) * (t + 1), ?_⟩
      -- Step 3.3.2: Rewrite (k + 1) in terms of t and factor out the 8 explicitly.
      calc
        4 * k * (k + 1)
            = 4 * (2 * t + 1) * ((2 * t + 1) + 1) := by simp [ht2]
        _ = 4 * (2 * t + 1) * (2 * (t + 1)) := by
              simp [two_mul, add_comm, add_left_comm, add_assoc]
        _ = 8 * ((2 * t + 1) * (t + 1)) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
  -- Step 4: Combine the algebraic identity with the divisibility result.
  -- Step 4.1: Replace n^2 - 1 by the factored form and conclude the proof.
  simpa [hcalc] using hdiv
