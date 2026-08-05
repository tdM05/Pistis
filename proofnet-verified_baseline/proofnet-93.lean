import Mathlib

open Polynomial
open scoped BigOperators



/-Informal Statement

Prove that $x^3 - 3x - 1$ is irreducible over $\mathbb{Q}$.
-/

/-Informal Proof

Let $p(x)=x^3-3 x-1$. Then
$$
p(x+1)=(x+1)^3-3(x+1)-1=x^3+3 x^2-3
$$
We have $3|3,3| 0$ but $3 \nmid 1$ and $3^2 \nmid 3$. Thus the polynomial is irreducible over $\mathbb{Q}$ by 3 -Eisenstein criterion.
-/

theorem Herstein_exercise_5_5_2 : Irreducible (X^3 - 3*X - 1 : Polynomial ℚ) := by
  classical
  -- Step 1: Set up a convenient name for the polynomial we study.
  let p : Polynomial ℚ := X ^ 3 - 3 * X - 1
  have hp_def : p = X ^ 3 - 3 * X - 1 := rfl
  -- Step 1.0: Name the lower-degree tail so all rewrites stay consistent.
  let tailQ : Polynomial ℚ := -3 * X - 1
  have htailQ_def : tailQ = -3 * X - 1 := rfl

  -- Step 1.1: Compute `natDegree p = 3` by comparing the dominant cubic term with the lower tail.
  have hp_natDegree : p.natDegree = 3 := by
    -- Step 1.1.1: Rewrite `p` as a sum of the cubic term and a lower-degree tail.
    have hrewrite : p = (X ^ 3 : Polynomial ℚ) + tailQ := by
      -- unfold and rearrange into a clear "dominant + tail" shape
      simp [p, tailQ, sub_eq_add_neg, add_comm, add_left_comm]
    -- Step 1.1.2: The tail `-3·X - 1` is linear.
    have htail_deg : tailQ.natDegree = 1 := by
      -- Step 1.1.2.1: The part `-3·X` has degree one because its scalar is nonzero.
      have hcoeff : (-3 : ℚ) ≠ 0 := by norm_num
      have hdeg_lin : (-3 * X : Polynomial ℚ).natDegree = 1 := by
        simp
      -- Step 1.1.2.2: The constant term has smaller degree, so adding it preserves the linear degree.
      have hconst_lt : (-1 : Polynomial ℚ).natDegree < (-3 * X : Polynomial ℚ).natDegree := by
        simp
      -- Step 1.1.2.3: Conclude the tail degree.
      calc
        tailQ.natDegree
            = ((-3 * X : Polynomial ℚ) + (-1)).natDegree := by
                simp [tailQ, sub_eq_add_neg, add_comm]
        _ = (-3 * X : Polynomial ℚ).natDegree :=
          Polynomial.natDegree_add_eq_left_of_natDegree_lt hconst_lt
        _ = 1 := hdeg_lin
    -- Step 1.1.3: The tail degree is strictly smaller than the cubic degree.
    have hdeg_main : (X ^ 3 : Polynomial ℚ).natDegree = 3 := by simp
    have htail_lt :
        tailQ.natDegree < (X ^ 3 : Polynomial ℚ).natDegree := by
      -- Reduce to the numeric inequality `1 < 3`.
      have hnum : (1 : ℕ) < 3 := by decide
      simp [htail_deg, hdeg_main, hnum]
    -- Step 1.1.4: Apply the degree lemma for sums with a smaller second summand.
    calc
      p.natDegree
          = ((X ^ 3 : Polynomial ℚ) + tailQ).natDegree := by
              simp [hrewrite]
      _ = (X ^ 3 : Polynomial ℚ).natDegree :=
        Polynomial.natDegree_add_eq_left_of_natDegree_lt htail_lt
      _ = 3 := by simp

  -- Step 1.2: Package the degree information inside the interval `[1, 3]`.
  have hp_deg_mem : p.natDegree ∈ Finset.Icc 1 3 := by
    simp [Finset.mem_Icc, hp_natDegree]

  -- Step 2: Switch to integer coefficients to deploy the rational-root test conveniently.
  let pZ : Polynomial ℤ := X ^ 3 - 3 * X - 1
  let tailZ : Polynomial ℤ := -3 * X - 1
  have htailZ_def : tailZ = -3 * X - 1 := rfl
  -- Step 2.1: Mapping `pZ` to ℚ recovers `p`.
  have hp_map : Polynomial.map (Int.castRingHom ℚ) pZ = p := by
    simp [pZ, hp_def]
  -- Step 2.2: The integer polynomial is monic.
  have hpZ_monic : Monic pZ := by
    -- Step 2.2.1: The integer tail is linear, hence of degree one.
    have htail_degZ : tailZ.natDegree = 1 := by
      have hcoeff : (-3 : ℤ) ≠ 0 := by norm_num
      have hdeg_lin : (-3 * X : Polynomial ℤ).natDegree = 1 := by
        simp
      have hconst_lt : (-1 : Polynomial ℤ).natDegree < (-3 * X : Polynomial ℤ).natDegree := by
        simp
      calc
        tailZ.natDegree
            = ((-3 * X : Polynomial ℤ) + (-1)).natDegree := by
                simp [tailZ, sub_eq_add_neg, add_comm]
        _ = (-3 * X : Polynomial ℤ).natDegree :=
          Polynomial.natDegree_add_eq_left_of_natDegree_lt hconst_lt
        _ = 1 := hdeg_lin
    -- Step 2.2.2: Translate `natDegree` information to `degree` inequalities.
    have htail_ne : tailZ ≠ 0 := by
      intro h
      have hcoeff0 : tailZ.coeff 0 = 0 := by simp [h]
      have hcoeff0' : tailZ.coeff 0 = (-1 : ℤ) := by simp [tailZ]
      linarith
    have hdeg_tail :
        Polynomial.degree tailZ = (1 : WithBot ℕ) := by
      simp [htail_degZ, Polynomial.degree_eq_natDegree htail_ne]
    have hdeg_main : Polynomial.degree (X ^ 3 : Polynomial ℤ) = (3 : WithBot ℕ) := by
      simp [Polynomial.degree_X_pow (R := ℤ) (n := 3)]
    have hdeg_ltZ :
        Polynomial.degree tailZ
          < Polynomial.degree (X ^ 3 : Polynomial ℤ) := by
      have hnum : (1 : WithBot ℕ) < (3 : WithBot ℕ) := by decide
      simp [hdeg_tail, hdeg_main, hnum]
    -- Step 2.2.3: Rewrite `pZ` as dominant cubic plus tail to read off the leading coefficient.
    have hrewriteZ : pZ = (X ^ 3 : Polynomial ℤ) + tailZ := by
      simp [pZ, tailZ, sub_eq_add_neg, add_comm, add_left_comm]
    have hlead :
        pZ.leadingCoeff = (X ^ 3 : Polynomial ℤ).leadingCoeff := by
      have hlead_eq :=
        Polynomial.leadingCoeff_add_of_degree_lt'
          (p := (X ^ 3 : Polynomial ℤ))
          (q := tailZ)
          hdeg_ltZ
      simpa [hrewriteZ] using hlead_eq
    -- Step 2.2.4: The cubic term is monic, so the whole polynomial is monic.
    have hlead_one : pZ.leadingCoeff = 1 := by
      simpa using hlead.trans (by simp : (X ^ 3 : Polynomial ℤ).leadingCoeff = 1)
    simpa [Monic] using hlead_one

  -- Step 3: Prove that `p` has no rational root.
  have hp_no_root : ∀ a : ℚ, ¬ IsRoot p a := by
    intro a ha
    -- Step 3.1: Rephrase the root condition with `aeval`.
    have h_aeval_rat : aeval a p = 0 := by
      simpa [IsRoot, Polynomial.coe_aeval_eq_eval] using ha
    -- Step 3.2: Transport the root to the integer polynomial using naturality of `aeval`.
    have hcompat :
        (algebraMap ℚ ℚ).comp (Int.castRingHom ℚ)
          = (RingHom.id ℚ).comp (algebraMap ℤ ℚ) := by
      ext z; simp
    have h_aeval_map :
        aeval a (Polynomial.map (Int.castRingHom ℚ) pZ) = 0 := by
      simpa [hp_map] using h_aeval_rat
    have h_aeval_int : aeval a pZ = 0 := by
      have hEq :=
        (map_aeval_eq_aeval_map (R := ℤ) (S := ℚ) (T := ℚ) (U := ℚ)
            (φ := Int.castRingHom ℚ) (ψ := RingHom.id ℚ) hcompat pZ a).symm
      simpa using hEq ▸ h_aeval_map
    -- Step 3.3: The integral root theorem gives an integer representative dividing the constant term.
    obtain ⟨m, hm_alg, hm_dvd⟩ :=
      exists_integer_of_is_root_of_monic (A := ℤ) (K := ℚ) hpZ_monic h_aeval_int
    -- Step 3.3.1: Replace `a` with that integer via the algebra map.
    have ha_int : a = algebraMap ℤ ℚ m := by simpa using hm_alg
    -- Step 3.3.2: Any divisor of `-1` must be `1` or `-1`.
    have hm_dvd_one : m ∣ (-1 : ℤ) := by
      simp [pZ] at hm_dvd ⊢; exact hm_dvd
    have hm_natAbs_dvd_one : m.natAbs ∣ 1 := by
      have hInt : (m.natAbs : ℤ) ∣ (1 : ℤ) :=
        (Int.natAbs_dvd).2 ((Int.dvd_neg).1 hm_dvd_one)
      exact (Int.natCast_dvd_natCast).1 hInt
    have hm_abs_one : m.natAbs = 1 := Nat.dvd_one.mp hm_natAbs_dvd_one
    have hm_cases : m = 1 ∨ m = -1 := Int.natAbs_eq_iff.mp hm_abs_one
    -- Step 3.4: Evaluate `p` at the two possible values and derive contradictions.
    cases hm_cases with
    | inl hm_one =>
        -- Substep 3.4.1: If `m = 1` then `a = 1`, but `p(1) = -3 ≠ 0`.
        have ha_one : a = 1 := by simp [ha_int, hm_one]
        have h_eval_one : p.eval 1 = 0 := by simpa [ha_one] using ha
        have h_value_one : p.eval 1 = (-3 : ℚ) := by norm_num [hp_def]
        have : (0 : ℚ) = -3 := by simpa [h_value_one] using h_eval_one.symm
        exact (by norm_num : (-3 : ℚ) ≠ 0) this.symm
    | inr hm_neg_one =>
        -- Substep 3.4.2: If `m = -1` then `a = -1`, but `p(-1) = 1 ≠ 0`.
        have ha_neg_one : a = -1 := by simp [ha_int, hm_neg_one]
        have h_eval_neg_one : p.eval (-1) = 0 := by simpa [ha_neg_one] using ha
        have h_value_neg_one : p.eval (-1) = (1 : ℚ) := by norm_num [hp_def]
        have : (0 : ℚ) = 1 := by simpa [h_value_neg_one] using h_eval_neg_one.symm
        exact (by norm_num : (1 : ℚ) ≠ 0) this.symm

  -- Step 4: A cubic polynomial over a field is irreducible iff it has no root.
  have hp_irred : Irreducible p :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot hp_deg_mem hp_no_root
  -- Step 4.1: Translate back to the original expression.
  simp [hp_def] at hp_irred ⊢; exact hp_irred
