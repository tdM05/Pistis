import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that $x^4-4x^3+6$ is irreducible in $\mathbb{Z}[x]$.
-/

/-Informal Proof

$$
x^4-4 x^3+6
$$
The polynomial is irreducible by Eisenstein's Criterion since the prime $2$ doesn't divide the leading coefficient 2 divide coefficients of the low order term $-4,0,0$ but 6 is not divided by the square of 2.
-/

theorem Dummit_Foote_exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  -- Step 1: Work classically and name the polynomial plus the Eisenstein ideal.
  classical
  set f : Polynomial ℤ := (X^4 - 4*X^3 + Polynomial.C 6)
  set P : Ideal ℤ := Ideal.span {(2 : ℤ)}
  -- Step 2: Record that `(2)` is a prime ideal of `ℤ`.
  have hPprime : P.IsPrime := by
    -- Step 2.1: View `2` as a prime element inside the integers.
    have hPrimeInt : Prime (2 : ℤ) :=
      (Nat.prime_iff_prime_int).1 (by simpa using Nat.prime_two)
    -- Step 2.2: Convert prime elements into prime ideals of `ℤ`.
    have hTwoNeZero : (2 : ℤ) ≠ 0 := by decide
    exact (Ideal.span_singleton_prime hTwoNeZero).2 hPrimeInt
  -- Step 3: Isolate the lower-degree tail that will play against Eisenstein.
  set tail : Polynomial ℤ := (-4 : Polynomial ℤ) * X^3 + Polynomial.C 6
  have hf_decomp : f = X^4 + tail := by
    -- Step 3.1: Expand every subtraction as addition with `-` and regroup.
    simp [f, tail, sub_eq_add_neg, add_comm, add_left_comm]
  have hf_decomp' : f = tail + X^4 := by
    -- Step 3.2: Produce the symmetric version for later degree computations.
    simp [f, tail, sub_eq_add_neg, add_comm, add_left_comm]
  -- Step 4: Show that the tail has degree at most `3`, hence strictly below the degree of `X^4`.
  have hTail_deg_le :
      degree tail ≤ (3 : WithBot ℕ) := by
    -- Step 4.1: Bound each summand individually and combine them.
    have hTerm :
        degree ((-4 : Polynomial ℤ) * X^3) ≤ (3 : WithBot ℕ) := by
      simpa using (Polynomial.degree_C_mul_X_pow_le (n := 3) (a := (-4 : ℤ)))
    have hConst :
        degree (6 : Polynomial ℤ) ≤ (0 : WithBot ℕ) := by
      simpa using (Polynomial.degree_C_le (R := ℤ) (a := 6))
    have hMax :
        max (degree ((-4 : Polynomial ℤ) * X^3)) (degree (6 : Polynomial ℤ))
            ≤ (3 : WithBot ℕ) := by
      refine max_le ?_ ?_
      · exact hTerm
      ·
        have hZeroLeThree : (0 : WithBot ℕ) ≤ (3 : WithBot ℕ) := by
          exact_mod_cast (Nat.zero_le 3)
        exact hConst.trans hZeroLeThree
    have hAdd :=
      Polynomial.degree_add_le ((-4 : Polynomial ℤ) * X^3) (6 : Polynomial ℤ)
    simpa [tail] using hAdd.trans hMax
  have hTail_deg_lt :
      degree tail < degree (X^4 : Polynomial ℤ) := by
    -- Step 4.2: Compare `≤ 3` with the known degree `4` of `X^4`.
    have hXdeg : degree (X^4 : Polynomial ℤ) = (4 : WithBot ℕ) := by
      simp [Polynomial.degree_X_pow (R := ℤ) (n := 4)]
    have h3lt4' : (3 : WithBot ℕ) < degree (X^4 : Polynomial ℤ) := by
      simpa [hXdeg] using (by exact_mod_cast (Nat.lt_succ_self 3))
    exact lt_of_le_of_lt hTail_deg_le h3lt4'
  -- Step 5: Compute the degree and leading coefficient of `f`.
  have hDegree :
      Polynomial.degree f = (4 : WithBot ℕ) := by
    -- Step 5.1: Use the additive decomposition where the highest term dominates.
    have := Polynomial.degree_add_eq_right_of_degree_lt hTail_deg_lt
    simpa [hf_decomp', add_comm] using this
  have hfLead :
      f.leadingCoeff = 1 := by
    -- Step 5.2: Invoke the matching lemma on leading coefficients.
    have hLeadEq :=
      Polynomial.leadingCoeff_add_of_degree_lt'
        (p := (X^4 : Polynomial ℤ))
        (q := tail)
        hTail_deg_lt
    have hLeadEq' :
        f.leadingCoeff = (X^4 : Polynomial ℤ).leadingCoeff := by
      simpa [hf_decomp] using hLeadEq
    have hxLead : ((X^4 : Polynomial ℤ).leadingCoeff) = 1 := by
      simp
    exact hLeadEq'.trans hxLead
  have hfMonic : Monic f := by
    -- Step 5.3: Convert the leading-coefficient computation into monicity.
    simpa using hfLead
  have hfPrim : f.IsPrimitive := hfMonic.isPrimitive
  -- Step 6: The leading coefficient is not in `(2)` because the ideal is proper.
  have hOneNot : (1 : ℤ) ∉ P :=
    (Ideal.ne_top_iff_one _).1 hPprime.ne_top
  have hLeadNot : f.leadingCoeff ∉ P := by
    -- Step 6.1: Substitute the explicit value `1`.
    simpa [hfLead] using hOneNot
  -- Step 7: Show that every lower coefficient lies inside `(2)`.
  have hCoeffs :
      ∀ m : ℕ, (m : WithBot ℕ) < Polynomial.degree f → f.coeff m ∈ P := by
    -- Step 7.1: Fix an arbitrary coefficient index below the degree bound.
    intro m hm
    -- Step 7.2: Translate the inequality into the concrete numeric bound `m < 4`.
    have hmLt : m < 4 := by
      have := (by simpa [hDegree] using hm :
        (m : WithBot ℕ) < (4 : WithBot ℕ))
      exact_mod_cast this
    -- Step 7.3: Exhaust the four possible indices via `interval_cases`.
    interval_cases m
    · -- Step 7.3.a: For `m = 0`, the coefficient equals `6`, which is divisible by `2`.
      have hCoeff0 : f.coeff 0 = 6 := by
        simp [f, sub_eq_add_neg]
      have hMul : (2 : ℤ) ∣ (6 : ℤ) := ⟨3, by norm_num⟩
      have hMem : (6 : ℤ) ∈ P := by
        simpa [P] using (Ideal.mem_span_singleton).2 hMul
      simpa [hCoeff0]
    · -- Step 7.3.b: When `m = 1`, the coefficient vanishes.
      have hCoeff1 : f.coeff 1 = 0 := by
        simp [f, sub_eq_add_neg]
      simp [hCoeff1]
    · -- Step 7.3.c: When `m = 2`, the coefficient still vanishes.
      have hCoeff2 : f.coeff 2 = 0 := by
        simp [f, sub_eq_add_neg]
      simp [hCoeff2]
    · -- Step 7.3.d: For `m = 3`, the coefficient is `-4`, again divisible by `2`.
      have hCoeff3 : f.coeff 3 = -4 := by
        simp [f, sub_eq_add_neg]
      have hMul : (2 : ℤ) ∣ (-4 : ℤ) := ⟨-2, by norm_num⟩
      have hMem : (-4 : ℤ) ∈ P := by
        simpa [P] using (Ideal.mem_span_singleton).2 hMul
      have hMemPos : (4 : ℤ) ∈ P := by
        simpa [Ideal.neg_mem_iff] using hMem
      simpa [hCoeff3]
  -- Step 8: Record that the polynomial has positive degree, here explicitly `4`.
  have hDegPos : 0 < Polynomial.degree f := by
    have : (0 : WithBot ℕ) < (4 : WithBot ℕ) := by
      exact_mod_cast (Nat.succ_pos 3)
    simp [hDegree, this]
  -- Step 9: Compute the constant coefficient and show it avoids `(2)^2`.
  have hfCoeff0 : f.coeff 0 = 6 := by
    simp [f, sub_eq_add_neg]
  have hConstNot : f.coeff 0 ∉ P ^ 2 := by
    -- Step 9.1: Convert membership in `P²` into divisibility by `4`.
    intro hMem
    obtain ⟨k, hk⟩ :=
      (Ideal.mem_span_singleton).1
        (by
          simpa [P, Ideal.span_singleton_pow, hfCoeff0] using hMem)
    -- Step 9.2: Translate the integer divisibility statement into `ℕ`.
    have hNatDiv : (4 : ℕ) ∣ 6 := by
      have hAbs := congrArg Int.natAbs hk
      have hPow : Int.natAbs ((2 : ℤ) ^ 2) = (4 : ℕ) := by
        simp [pow_two]
      refine ⟨Int.natAbs k, ?_⟩
      simpa [Int.natAbs_mul, Int.natAbs_natCast, hPow] using hAbs
    -- Step 9.3: Conclude via the numerically obvious impossibility `4 ∤ 6`.
    have hNot : ¬ (4 : ℕ) ∣ 6 := by decide
    exact hNot hNatDiv
  -- Step 10: Apply Eisenstein's criterion and translate back to the original statement.
  have hIrred :
      Irreducible f :=
    Polynomial.irreducible_of_eisenstein_criterion
      (f := f)
      (P := P)
      hPprime
      hLeadNot
      hCoeffs
      hDegPos
      hConstNot
      hfPrim
  -- Step 11: Undo the `set` abbreviation.
  simpa [f]
