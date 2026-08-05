-- Authors: marcusm117
-- License: Apache 2.0


import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Prove that $x^2+1$ is irreducible in $\mathbb{F}_7$
-/

/-Informal Proof

If $p(x)=x^2+1$ were reducible, its factors must be linear. But no $p(a)$ for $a\in\mathbb{F}_7$ evaluates to 0, therefore $x^2+1$ is irreducible.
-/

theorem Artin_exercise_11_4_6b {F : Type*} [Field F] [Fintype F] (hF : card F = 7) :
  Irreducible (X ^ 2 + 1 : Polynomial F) := by
  -- Step 1: Switch to classical logic and analyse the arithmetic of the field.
  classical
  -- Step 1.1: Record that the cardinality is odd, namely `7 ≡ 1 (mod 2)`.
  have hOdd : Fintype.card F % 2 = 1 := by
    -- Step 1.1.1: Compute the parity of seven directly.
    have : 7 % 2 = 1 := by decide
    -- Step 1.1.2: Transport the numerical identity to the field using the given cardinality.
    simp [hF]
  -- Step 1.2: Deduce that the characteristic cannot be two.
  have hChar_ne_two : ringChar F ≠ 2 := by
    -- Step 1.2.1: Assume, for contradiction, that the characteristic is two.
    intro hChar
    -- Step 1.2.2: Use the standard parity lemma for finite fields of characteristic two.
    have hEven : Fintype.card F % 2 = 0 :=
      FiniteField.even_card_of_char_two (F := F) hChar
    -- Step 1.2.3: Contradict the parity computation from Step 1.1.
    simp [hOdd] at hEven
  -- Step 2: Record the structural data of the polynomial `X^2 + 1`.
  have hMonic : Monic (X ^ 2 + 1 : Polynomial F) := by
    -- Step 2.1: Use the general lemma for monicity of `X^n + C a`.
    simpa using
      (Polynomial.monic_X_pow_add_C (R := F) (n := 2) (a := (1 : F)) (by decide : (2 : ℕ) ≠ 0))
  -- Step 2.2: Note that the polynomial has degree two.
  have hNatDegree :
      (X ^ 2 + 1 : Polynomial F).natDegree = 2 := by
    -- Step 2.2.1: Apply the ready-made formula for the degree of `X^n + C r`.
    simpa using
      (Polynomial.natDegree_X_pow_add_C (R := F) (n := 2) (r := (1 : F)))
  -- Step 3: Suppose (for contradiction) that the polynomial is reducible.
  by_contra hReducible
  -- Step 3.1: Extract the linear factor data provided by the degree-two reducibility criterion.
  obtain ⟨c₁, c₂, hConst, hLinear⟩ :=
    (Polynomial.Monic.not_irreducible_iff_exists_add_mul_eq_coeff
        (p := (X ^ 2 + 1 : Polynomial F)) hMonic hNatDegree).mp hReducible
  -- Step 3.2: Simplify the constant-term identity to `c₁ * c₂ = 1`.
  have hMul : c₁ * c₂ = (1 : F) := by
    -- Step 3.2.1: The constant coefficient of `X^2 + 1` is exactly `1`.
    simpa using hConst.symm
  -- Step 3.3: Simplify the coefficient of `X` to `c₁ + c₂ = 0`.
  have hSum : c₁ + c₂ = (0 : F) := by
    -- Step 3.3.1: The coefficient of `X` in `X^2 + 1` vanishes.
    have hCoeff : (X ^ 2 + 1 : Polynomial F).coeff 1 = (0 : F) := by
      -- Step 3.3.1.1: Evaluate the coefficient using the standard formula for `X^n`.
      -- Step 3.3.1.1.1: Decompose the coefficient of the sum into a sum of coefficients.
      have hCoeffAdd :
          (X ^ 2 + 1 : Polynomial F).coeff 1
            = (X ^ 2 : Polynomial F).coeff 1 + (1 : Polynomial F).coeff 1 := by
        simp
      -- Step 3.3.1.1.2: Compute the first addend, the coefficient of `X` in `X^2`.
      have hCoeffX : (X ^ 2 : Polynomial F).coeff 1 = (0 : F) := by
        simp [Polynomial.coeff_X_pow]
      -- Step 3.3.1.1.3: Compute the second addend, the coefficient of `X` in the constant polynomial `1`.
      have hCoeffOne : (1 : Polynomial F).coeff 1 = (0 : F) := by
        -- Step 3.3.1.1.3.1: Apply the ready-made lemma for coefficients of constant polynomials.
        simpa using (Polynomial.coeff_C_succ (r := (1 : F)) (n := 0))
      -- Step 3.3.1.1.4: Combine the evaluations to obtain the desired zero.
      calc
        (X ^ 2 + 1 : Polynomial F).coeff 1
            = (X ^ 2 : Polynomial F).coeff 1 + (1 : Polynomial F).coeff 1 := hCoeffAdd
        _ = (0 : F) := by simp [hCoeffX, hCoeffOne]
    -- Step 3.3.2: Substitute the vanishing coefficient into the linear identity.
    simpa [hCoeff] using hLinear.symm
  -- Step 3.4: Show that neither `c₁` nor `c₂` can be zero.
  have hC₁_ne : c₁ ≠ 0 := by
    -- Step 3.4.1: Zero would contradict the unit equation `c₁ * c₂ = 1`.
    intro hZero
    simp [hZero] at hMul
  -- Step 3.5: Rewrite `c₂` in terms of `c₁` using the vanishing sum.
  have hC₂_eq : c₂ = -c₁ := eq_neg_of_add_eq_zero_right hSum
  -- Step 3.6: Convert the product identity into the square relation `c₁^2 = -1`.
  have hNegSquare : -(c₁ ^ 2) = (1 : F) := by
    -- Step 3.6.1: Replace `c₂` by `-c₁` and simplify the product.
    simpa [hC₂_eq, pow_two, mul_comm, mul_left_comm, mul_assoc] using hMul
  -- Step 3.6.2: Remove the leading minus sign to obtain the square relation explicitly.
  have hSquare : c₁ ^ 2 = (-1 : F) := by
    -- Step 3.6.2.1: Negate both sides of the previous identity.
    have := congrArg (fun x : F => -x) hNegSquare
    -- Step 3.6.2.2: Simplify the resulting double negation.
    simpa [neg_neg] using this
  -- Step 4: Analyse the multiplicative order consequences of `c₁^2 = -1`.
  have hPowCard :
      c₁ ^ 6 = (1 : F) := by
    -- Step 4.1: Apply the finite field Fermat's little theorem with `|F| = 7`.
    simpa [hF] using
      (FiniteField.pow_card_sub_one_eq_one (K := F) c₁ hC₁_ne)
  -- Step 4.2: Compute the sixth power again using the square equation.
  have hPowSquare : c₁ ^ 6 = (-1 : F) := by
    -- Step 4.2.1: Express the sixth power as `(c₁^2)^3`.
    have hSix : (6 : ℕ) = 2 * 3 := by decide
    -- Step 4.2.1.1: Rewrite the sixth power via the multiplicative law for exponents.
    have hPowRewrite : c₁ ^ 6 = (c₁ ^ 2) ^ 3 := by
      simpa [hSix] using (pow_mul (a := c₁) (m := 2) (n := 3))
    -- Step 4.2.2: Raise the square identity to the third power.
    have hCube : (c₁ ^ 2) ^ 3 = (-1 : F) ^ 3 := by
      simpa using congrArg (fun x : F => x ^ 3) hSquare
    -- Step 4.2.3: Evaluate the cube of `-1`.
    have hCubeEval : (-1 : F) ^ 3 = (-1 : F) := by
      -- Step 4.2.3.1: Expand the cube of `-1` explicitly.
      simp [pow_succ]
    -- Step 4.2.4: Combine the equalities to obtain the sixth power.
    calc
      c₁ ^ 6 = (c₁ ^ 2) ^ 3 := hPowRewrite
      _ = (-1 : F) ^ 3 := hCube
      _ = (-1 : F) := hCubeEval
  -- Step 4.3: Combine the two sixth-power computations to force `1 = -1`.
  have hOne_eq_negOne : (1 : F) = (-1 : F) := by
    -- Step 4.3.1: Use the equality from Step 4.1 as the bridge.
    calc
      (1 : F) = c₁ ^ 6 := by simpa using hPowCard.symm
      _ = (-1 : F) := hPowSquare
  -- Step 5: Reach the contradiction with the characteristic analysis from Step 1.
  exact (Ring.neg_one_ne_one_of_char_ne_two hChar_ne_two) hOne_eq_negOne.symm
