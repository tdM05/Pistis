import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Prove that $f(x) = x^3 + 3x + 2$ is irreducible in $Q[x]$.
-/

/-Informal Proof

Let us assume that $f(x)$ is reducible over $\mathbb{Q}[x]$.
Then there exists a rational root of $f(x)$.
Let $p / q$ be a rational root of $f(x)$, where $\operatorname{gcd}(p, q)=1$.
Then $f(p / q)=0$.
Now,
$$
\begin{aligned}
& f(p / q)=(p / q)^3+3(p / q)+2 \\
\Longrightarrow & (p / q)^3+3(p / q)+2=0 \\
\Longrightarrow & p^3+3 p q^2=-2 q^3 \\
\Longrightarrow & p\left(p^2+3 q^2\right)=-q^3
\end{aligned}
$$
It follows that, $p$ divides $q$ which is a contradiction to the fact that $\operatorname{gcd}(p, q)=1$.
This implies that $f(x)$ has no rational root.
Now we know that, a polynomial of degree two or three over a field $F$ is reducible if and only if it has a root in $F$.
Now $f(x)$ is a 3 degree polynomial having no root in $\mathbb{Q}$.
So, $f(x)$ is irreducible in $\mathbb{Q}[x]$.
This completes the proof.
-/

theorem Herstein_exercise_4_6_2 : Irreducible (X^3 + 3*X + 2 : Polynomial ℚ) := by
  classical
  -- Step 1: Introduce the target polynomial `f` and keep track of its definition for later rewrites.
  let f : Polynomial ℚ := X ^ 3 + 3 * X + 2
  have hf_def : f = X ^ 3 + 3 * X + 2 := rfl
  -- Step 1.1: Compute the natural degree of `f` by isolating the leading cubic term.
  have hf_natDegree : f.natDegree = 3 := by
    -- Step 1.1.1: The cubic monomial has degree three.
    have hdeg_cube : ((X : Polynomial ℚ) ^ 3).natDegree = 3 := by
      simp
    -- Step 1.1.2: The tail `3·X + 2` has degree exactly one.
    have hdeg_tail : (3 * X + 2 : Polynomial ℚ).natDegree = 1 := by
      -- Step 1.1.2.1: Degree of `3·X` is exactly one.
      have hthree : (3 : ℚ) ≠ 0 := by norm_num
      have hdeg_3X : (3 * X : Polynomial ℚ).natDegree = 1 := by
        simp
      -- Step 1.1.2.2: Degree of the constant term is zero, hence strictly smaller than one.
      have hconst_lt : (2 : Polynomial ℚ).natDegree < (3 * X : Polynomial ℚ).natDegree := by
        simp [hdeg_3X]
      -- Step 1.1.2.3: Apply the comparison lemma for sums.
      simpa using
        (Polynomial.natDegree_add_eq_left_of_natDegree_lt
          (p := (3 * X : Polynomial ℚ)) (q := (2 : Polynomial ℚ)) hconst_lt)
    -- Step 1.1.3: Therefore `tail` has degree strictly smaller than the cubic part.
    have hlt : (3 * X + 2 : Polynomial ℚ).natDegree < 3 := by
      -- numerical inequality `1 < 3`
      simp [hdeg_tail]
    have hlt' :
        (3 * X + 2 : Polynomial ℚ).natDegree < (X ^ 3 : Polynomial ℚ).natDegree := by
      simpa [hdeg_cube] using hlt
    -- Step 1.1.4: Rewrite `f` as `X^3 + tail`.
    have hf_rewrite : f = X ^ 3 + (3 * X + 2) := by ring
    -- Step 1.1.5: Apply the degree lemma for sums with a smaller second addend.
    calc
      f.natDegree = (X ^ 3 + (3 * X + 2 : Polynomial ℚ)).natDegree := by
        simp [hf_rewrite]
      _ = (X ^ 3 : Polynomial ℚ).natDegree :=
        (Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt')
      _ = 3 := hdeg_cube
  -- Step 1.2: Package the degree information in the interval `[1, 3]` for the irreducibility lemma.
  have hf_deg_mem : f.natDegree ∈ Finset.Icc 1 3 := by
    -- Step 1.2.1: Since `natDegree f = 3`, inclusion in the closed interval is immediate.
    simp [Finset.mem_Icc, hf_natDegree]
  -- Step 2: Create an integer polynomial `fZ` whose coefficients agree with those of `f`.
  let fZ : Polynomial ℤ := X ^ 3 + 3 * X + 2
  -- Step 2.1: Relate `fZ` back to `f` via the canonical map from `ℤ` to `ℚ`.
  have hf_map : Polynomial.map (Int.castRingHom ℚ) fZ = f := by
    -- Step 2.1.1: Mapping preserves addition and multiplication, so this is a straightforward simplification.
    simp [fZ, hf_def]
  -- Step 2.2: Observe that `fZ` is monic, enabling the integral root theorem.
  have hfZ_monic : Monic fZ := by
    -- Step 2.2.1: Compute the degree of `fZ`, mirroring the rational case.
    have hthreeZ : (3 : ℤ) ≠ 0 := by norm_num
    have hdeg_3X : (3 * X : Polynomial ℤ).natDegree = 1 := by
      simp
    have hconst_lt : (2 : Polynomial ℤ).natDegree < (3 * X : Polynomial ℤ).natDegree := by
      simp [hdeg_3X]
    have hdeg_tail : (3 * X + 2 : Polynomial ℤ).natDegree = 1 := by
      simpa using
        (Polynomial.natDegree_add_eq_left_of_natDegree_lt
          (p := (3 * X : Polynomial ℤ)) (q := (2 : Polynomial ℤ)) hconst_lt)
    have hlt' :
        (3 * X + 2 : Polynomial ℤ).natDegree < (X ^ 3 : Polynomial ℤ).natDegree := by
      -- numerical inequality again `1 < 3`
      simp [hdeg_tail]
    have hfZ_rewrite : fZ = X ^ 3 + (3 * X + 2) := by ring
    have hfZ_natDegree : fZ.natDegree = 3 := by
      calc
        fZ.natDegree = (X ^ 3 + (3 * X + 2 : Polynomial ℤ)).natDegree := by
          simp [hfZ_rewrite]
        _ = (X ^ 3 : Polynomial ℤ).natDegree :=
          (Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt')
        _ = 3 := by simp
    -- Step 2.2.2: Use the coefficient at degree three to conclude monicity.
    -- Step 2.2.3: Extract the leading coefficient from the degree and the coefficient computation.
    have hcoeff : fZ.coeff 3 = 1 := by simp [fZ, coeff_X]
    have hlead : fZ.leadingCoeff = 1 := by
      calc
        fZ.leadingCoeff = fZ.coeff fZ.natDegree := (coeff_natDegree (p := fZ)).symm
        _ = fZ.coeff 3 := by simp [hfZ_natDegree]
        _ = 1 := hcoeff
    exact hlead
  -- Step 3: Show that `f` has no rational roots by pulling any hypothetical root back to `ℤ`.
  have hf_no_root : ∀ a : ℚ, ¬ IsRoot f a := by
    -- Step 3.1: Fix a rational number `a` and assume it is a root to derive a contradiction.
    intro a ha
    -- Step 3.1.1: Convert the root statement to the `aeval` formulation, which interacts cleanly with maps.
    have h_aeval_rat : aeval a f = 0 := by
      simpa [IsRoot, Polynomial.coe_aeval_eq_eval] using ha
    -- Step 3.1.2: Record the compatibility between the relevant algebra maps used in `map_aeval_eq_aeval_map`.
    have hcompat :
        (algebraMap ℚ ℚ).comp (Int.castRingHom ℚ)
          = (RingHom.id ℚ).comp (algebraMap ℤ ℚ) := by
      -- Step 3.1.2.1: This follows from functoriality of the algebra maps.
      ext z; simp
    -- Step 3.1.3: Transport the root to the mapped integer polynomial.
    have h_aeval_map :
        aeval a (Polynomial.map (Int.castRingHom ℚ) fZ) = 0 := by
      simpa [hf_map] using h_aeval_rat
    -- Step 3.1.4: Pull the root all the way back to `fZ`.
    have h_aeval_int : aeval a fZ = 0 := by
      -- Step 3.1.4.1: Use the naturality of `aeval`.
      have hEq :=
        (map_aeval_eq_aeval_map (R := ℤ) (S := ℚ) (T := ℚ) (U := ℚ)
            (φ := Int.castRingHom ℚ) (ψ := RingHom.id ℚ) hcompat fZ a).symm
      simpa using hEq ▸ h_aeval_map
    -- Step 3.2: Apply the integral root theorem to extract an integer representative of the root.
    obtain ⟨m, hm_alg, hm_dvd⟩ :=
      exists_integer_of_is_root_of_monic (A := ℤ) (K := ℚ) hfZ_monic h_aeval_int
    -- Step 3.2.1: Translate the original root into an evaluation at `algebraMap ℤ ℚ m`.
    have h_eval_m : f.eval (algebraMap ℤ ℚ m) = 0 := by
      simpa [IsRoot, Polynomial.coe_aeval_eq_eval, hm_alg] using ha
    -- Step 3.2.2: The integral root theorem also tells us that `m` divides the constant term `2`.
    have hm_dvd_two : m ∣ (2 : ℤ) := by
      simpa [fZ] using hm_dvd
    -- Step 3.3: Convert that divisibility into a statement about the natural absolute value.
    have hm_natAbs_dvd_two : m.natAbs ∣ 2 := by
      -- Step 3.3.1: Move from integer divisibility to natural-number divisibility.
      have hInt : (m.natAbs : ℤ) ∣ (2 : ℤ) := (Int.natAbs_dvd).2 hm_dvd_two
      exact (Int.natCast_dvd_natCast).1 hInt
    -- Step 3.4: Exploit the fact that `2` is prime in `ℕ` to enumerate the possibilities for `|m|`.
    have hm_abs_cases : m.natAbs = 1 ∨ m.natAbs = 2 :=
      (Nat.dvd_prime Nat.prime_two).1 hm_natAbs_dvd_two
    -- Step 3.5: Finish by ruling out each possible value of `m`.
    cases hm_abs_cases with
    | inl hm_abs_one =>
        -- Step 3.5.1: From `|m| = 1` deduce `m = 1` or `m = -1`.
        have hm_vals : m = 1 ∨ m = -1 := by
          have hm_pos_or_neg : 0 ≤ m ∨ m ≤ 0 := le_total 0 m
          cases hm_pos_or_neg with
          | inl hnonneg =>
              -- Step 3.5.1.1: When `m ≥ 0`, absolute value equals the number itself.
              have hm_eq :
                  m = 1 := by
                    have hceq :
                        m.natAbs = (1 : ℤ).natAbs := by simp [hm_abs_one]
                    -- Step 3.5.1.1.1: Use injectivity of `natAbs` on non-negative integers.
                    exact (Int.natAbs_inj_of_nonneg_of_nonneg hnonneg (by decide)).1 hceq
              exact Or.inl hm_eq
          | inr hnonpos =>
              -- Step 3.5.1.2: When `m ≤ 0`, convert the absolute value equation to `-m = 1`.
              have hceq :
                  m.natAbs = (1 : ℤ).natAbs := by simp [hm_abs_one]
              have h_neg :
                  -m = 1 := (Int.natAbs_inj_of_nonpos_of_nonneg hnonpos (by decide)).1 hceq
              have hm_eq : m = -1 := by linarith
              exact Or.inr hm_eq
        -- Step 3.5.2: Evaluate the polynomial at both integer possibilities and reach contradictions.
        cases hm_vals with
        | inl hm_one =>
            -- Step 3.5.2.1: Evaluate at `1`.
            have h_eval_one : f.eval (1 : ℚ) = 0 := by
              simpa [hm_one] using h_eval_m
            have h_value_one : f.eval (1 : ℚ) = 6 := by
              norm_num [hf_def]
            -- Step 3.5.2.1.1: Contradiction since `6 ≠ 0`.
            have : (6 : ℚ) = 0 := by simp [h_value_one] at h_eval_one
            exact (by norm_num : (6 : ℚ) ≠ 0) this
        | inr hm_neg_one =>
            -- Step 3.5.2.2: Evaluate at `-1`.
            have h_eval_neg_one : f.eval (-1 : ℚ) = 0 := by
              simpa [hm_neg_one] using h_eval_m
            have h_value_neg_one : f.eval (-1 : ℚ) = (-2 : ℚ) := by
              norm_num [hf_def]
            -- Step 3.5.2.2.1: Contradiction since `-2 ≠ 0`.
            have : (-2 : ℚ) = 0 := by simp [h_value_neg_one] at h_eval_neg_one
            exact (by norm_num : (-2 : ℚ) ≠ 0) this
    | inr hm_abs_two =>
        -- Step 3.5.3: From `|m| = 2` deduce `m = 2` or `m = -2`.
        have hm_vals : m = 2 ∨ m = -2 := by
          have hm_pos_or_neg : 0 ≤ m ∨ m ≤ 0 := le_total 0 m
          cases hm_pos_or_neg with
          | inl hnonneg =>
              have hceq :
                  m.natAbs = (2 : ℤ).natAbs := by simp [hm_abs_two]
              have hm_eq : m = 2 :=
                (Int.natAbs_inj_of_nonneg_of_nonneg hnonneg (by decide)).1 hceq
              exact Or.inl hm_eq
          | inr hnonpos =>
              have hceq :
                  m.natAbs = (2 : ℤ).natAbs := by simp [hm_abs_two]
              have h_neg :
                  -m = 2 :=
                (Int.natAbs_inj_of_nonpos_of_nonneg hnonpos (by decide)).1 hceq
              have hm_eq : m = -2 := by linarith
              exact Or.inr hm_eq
        -- Step 3.5.4: Evaluate the polynomial at both integer possibilities and reach contradictions.
        cases hm_vals with
        | inl hm_two =>
            -- Step 3.5.4.1: Evaluate at `2`.
            have h_eval_two : f.eval (2 : ℚ) = 0 := by
              simpa [hm_two] using h_eval_m
            have h_value_two : f.eval (2 : ℚ) = (16 : ℚ) := by
              norm_num [hf_def]
            -- Step 3.5.4.1.1: Contradiction since `16 ≠ 0`.
            have : (16 : ℚ) = 0 := by simp [h_value_two] at h_eval_two
            exact (by norm_num : (16 : ℚ) ≠ 0) this
        | inr hm_neg_two =>
            -- Step 3.5.4.2: Evaluate at `-2`.
            have h_eval_neg_two : f.eval (-2 : ℚ) = 0 := by
              simpa [hm_neg_two] using h_eval_m
            have h_value_neg_two : f.eval (-2 : ℚ) = (-12 : ℚ) := by
              norm_num [hf_def]
            -- Step 3.5.4.2.1: Contradiction since `-12 ≠ 0`.
            have : (-12 : ℚ) = 0 := by simp [h_value_neg_two] at h_eval_neg_two
            exact (by norm_num : (-12 : ℚ) ≠ 0) this
  -- Step 4: Combine the absence of rational roots with the cubic degree bound to conclude irreducibility.
  have hf_irred :
      Irreducible f :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot hf_deg_mem hf_no_root
  -- Step 4.1: Translate the result back to the original polynomial expression.
  simpa [hf_def] using hf_irred
