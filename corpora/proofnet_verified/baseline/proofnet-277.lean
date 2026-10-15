import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

set_option maxHeartbeats 800000

noncomputable section

/-- √k is integral over ℚ since (√k)² = k -/
lemma isIntegral_sqrt_nat (k : ℕ) : IsIntegral ℚ (Real.sqrt k : ℂ) := by
  apply IsIntegral.of_pow (n := 2) (by norm_num : 0 < 2)
  have h : (Real.sqrt k : ℂ)^2 = (k : ℂ) := by
    rw [sq, ← Complex.ofReal_mul]; congr 1; exact Real.mul_self_sqrt (Nat.cast_nonneg k)
  rw [h]
  exact isAlgebraic_iff_isIntegral.mp (by exact_mod_cast isAlgebraic_nat (R := ℚ) k)

/-- K = ℚ(√2, √5, √7, √11) -/
def K : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ),
                               (Real.sqrt 7 : ℂ), (Real.sqrt 11 : ℂ)}

lemma K_isAlgebraic : Algebra.IsAlgebraic ℚ K := by
  apply IntermediateField.isAlgebraic_adjoin
  intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    [exact isIntegral_sqrt_nat 2; exact isIntegral_sqrt_nat 5;
     exact isIntegral_sqrt_nat 7; exact isIntegral_sqrt_nat 11]

instance K_isIntegral : Algebra.IsIntegral ℚ K := by
  rw [Algebra.isIntegral_def]; intro x
  exact isAlgebraic_iff_isIntegral.mp (K_isAlgebraic.isAlgebraic x)

lemma sqrt2_mem_K : (Real.sqrt 2 : ℂ) ∈ K := by
  unfold K; apply IntermediateField.subset_adjoin; left; rfl
lemma sqrt5_mem_K : (Real.sqrt 5 : ℂ) ∈ K := by
  unfold K; apply IntermediateField.subset_adjoin; right; left; rfl
lemma sqrt7_mem_K : (Real.sqrt 7 : ℂ) ∈ K := by
  unfold K; apply IntermediateField.subset_adjoin; right; right; left; rfl
lemma sqrt11_mem_K : (Real.sqrt 11 : ℂ) ∈ K := by
  unfold K; apply IntermediateField.subset_adjoin; right; right; right; rfl

/-- p(X) = X⁵ + √2·X³ + √5·X² + √7·X + √11 over ℂ -/
def p_C : Polynomial ℂ :=
  X^5 + C (Real.sqrt 2 : ℂ) * X^3 + C (Real.sqrt 5 : ℂ) * X^2 +
  C (Real.sqrt 7 : ℂ) * X + C (Real.sqrt 11 : ℂ)

lemma p_C_monic : p_C.Monic := by
  unfold p_C
  have h5 : (X^5 : Polynomial ℂ).Monic := monic_X_pow 5
  have h53 : (X^5 + C (Real.sqrt 2 : ℂ) * X^3 : Polynomial ℂ).Monic := by
    apply Monic.add_of_left h5
    calc (C (Real.sqrt 2 : ℂ) * X^3 : Polynomial ℂ).degree
        ≤ (C (Real.sqrt 2 : ℂ)).degree + (X^3).degree := degree_mul_le _ _
      _ ≤ 0 + 3 := add_le_add degree_C_le (le_of_eq (degree_X_pow 3))
      _ = (3 : ℕ) := by ring
      _ < (5 : ℕ) := by norm_num
      _ = (X^5 : Polynomial ℂ).degree := (degree_X_pow 5).symm
  have hd53 : (X^5 + C (Real.sqrt 2 : ℂ) * X^3 : Polynomial ℂ).degree = 5 := by
    rw [degree_add_eq_left_of_degree_lt]
    · simp only [degree_X_pow]; norm_cast
    · calc (C (Real.sqrt 2 : ℂ) * X^3 : Polynomial ℂ).degree
          ≤ (C (Real.sqrt 2 : ℂ)).degree + (X^3).degree := degree_mul_le _ _
        _ ≤ 0 + 3 := add_le_add degree_C_le (le_of_eq (degree_X_pow 3))
        _ = (3 : ℕ) := by ring
        _ < (5 : ℕ) := by norm_num
        _ = (X^5 : Polynomial ℂ).degree := (degree_X_pow 5).symm
  have h532 : (X^5 + C (Real.sqrt 2 : ℂ) * X^3 + C (Real.sqrt 5 : ℂ) * X^2 : Polynomial ℂ).Monic := by
    apply Monic.add_of_left h53
    calc (C (Real.sqrt 5 : ℂ) * X^2 : Polynomial ℂ).degree
        ≤ (C (Real.sqrt 5 : ℂ)).degree + (X^2).degree := degree_mul_le _ _
      _ ≤ 0 + 2 := add_le_add degree_C_le (le_of_eq (degree_X_pow 2))
      _ = (2 : ℕ) := by ring
      _ < (5 : ℕ) := by norm_num
      _ = (X^5 + C (Real.sqrt 2 : ℂ) * X^3 : Polynomial ℂ).degree := hd53.symm
  have hd532 : (X^5 + C (Real.sqrt 2 : ℂ) * X^3 + C (Real.sqrt 5 : ℂ) * X^2 : Polynomial ℂ).degree = 5 := by
    rw [degree_add_eq_left_of_degree_lt]
    · exact hd53
    · calc (C (Real.sqrt 5 : ℂ) * X^2 : Polynomial ℂ).degree
          ≤ (C (Real.sqrt 5 : ℂ)).degree + (X^2).degree := degree_mul_le _ _
        _ ≤ 0 + 2 := add_le_add degree_C_le (le_of_eq (degree_X_pow 2))
        _ = (2 : ℕ) := by ring
        _ < (5 : ℕ) := by norm_num
        _ = (X^5 + C (Real.sqrt 2 : ℂ) * X^3 : Polynomial ℂ).degree := hd53.symm
  have h5321 : (X^5 + C (Real.sqrt 2 : ℂ) * X^3 + C (Real.sqrt 5 : ℂ) * X^2 +
                C (Real.sqrt 7 : ℂ) * X : Polynomial ℂ).Monic := by
    apply Monic.add_of_left h532
    calc (C (Real.sqrt 7 : ℂ) * X : Polynomial ℂ).degree
        ≤ (C (Real.sqrt 7 : ℂ)).degree + X.degree := degree_mul_le _ _
      _ ≤ 0 + 1 := add_le_add degree_C_le degree_X_le
      _ = (1 : ℕ) := by ring
      _ < (5 : ℕ) := by norm_num
      _ = (X^5 + C (Real.sqrt 2 : ℂ) * X^3 + C (Real.sqrt 5 : ℂ) * X^2 : Polynomial ℂ).degree := hd532.symm
  have hd5321 : (X^5 + C (Real.sqrt 2 : ℂ) * X^3 + C (Real.sqrt 5 : ℂ) * X^2 +
                 C (Real.sqrt 7 : ℂ) * X : Polynomial ℂ).degree = 5 := by
    rw [degree_add_eq_left_of_degree_lt]
    · exact hd532
    · calc (C (Real.sqrt 7 : ℂ) * X : Polynomial ℂ).degree
          ≤ (C (Real.sqrt 7 : ℂ)).degree + X.degree := degree_mul_le _ _
        _ ≤ 0 + 1 := add_le_add degree_C_le degree_X_le
        _ = (1 : ℕ) := by ring
        _ < (5 : ℕ) := by norm_num
        _ = (X^5 + C (Real.sqrt 2 : ℂ) * X^3 + C (Real.sqrt 5 : ℂ) * X^2 : Polynomial ℂ).degree := hd532.symm
  apply Monic.add_of_left h5321
  calc (C (Real.sqrt 11 : ℂ) : Polynomial ℂ).degree ≤ 0 := degree_C_le
    _ < (5 : ℕ) := by norm_num
    _ = (X^5 + C (Real.sqrt 2 : ℂ) * X^3 + C (Real.sqrt 5 : ℂ) * X^2 +
         C (Real.sqrt 7 : ℂ) * X : Polynomial ℂ).degree := hd5321.symm

/-- p(X) over K -/
def p_K : Polynomial K :=
  X^5 + C ⟨Real.sqrt 2, sqrt2_mem_K⟩ * X^3 + C ⟨Real.sqrt 5, sqrt5_mem_K⟩ * X^2 +
  C ⟨Real.sqrt 7, sqrt7_mem_K⟩ * X + C ⟨Real.sqrt 11, sqrt11_mem_K⟩

lemma p_K_map_eq : p_K.map (algebraMap K ℂ) = p_C := by
  simp only [p_K, p_C, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
             map_X, map_C]; rfl

lemma p_K_monic : p_K.Monic := by
  apply monic_of_injective (algebraMap K ℂ).injective
  rw [p_K_map_eq]; exact p_C_monic

def is_root_of_p (a : ℂ) : Prop :=
  a^5 + (Real.sqrt 2 : ℂ) * a^3 + (Real.sqrt 5 : ℂ) * a^2 +
  (Real.sqrt 7 : ℂ) * a + (Real.sqrt 11 : ℂ) = 0

lemma a_integral_over_K {a : ℂ} (ha : is_root_of_p a) : IsIntegral K a := by
  use p_K, p_K_monic
  show eval₂ (algebraMap K ℂ) a p_K = 0
  rw [← eval_map, p_K_map_eq]
  unfold p_C is_root_of_p at *
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
  exact ha

lemma a_integral_over_Q {a : ℂ} (ha : is_root_of_p a) : IsIntegral ℚ a :=
  @isIntegral_trans ℚ K ℂ _ _ _ _ _ _ _ K_isIntegral a (a_integral_over_K ha)

/-- Any rational can be written as a/b for integers -/
lemma rat_cast_eq_int_div (r : ℚ) : (r : ℂ) = (r.num : ℂ) / (r.den : ℂ) := by
  simp only [Rat.cast_def]

/-Informal Statement

If a ∈ ℂ satisfies p(a) = 0 where p(x) = x^5 + √2·x³ + √5·x² + √7·x + √11,
then a is algebraic over ℚ of degree at most 80.
-/

/-Informal Proof

Given $a \in \mathbb{C}$ such that $p(a)=0$, where
$$
p(x)=x^5+\sqrt{2} x^3+\sqrt{5} x^2+\sqrt{7} x+\sqrt{11}
$$
Here, we note that $p(x) \in \mathbb{Q}(\sqrt{2}, \sqrt{5}, \sqrt{7}, \sqrt{11})$ and
$$
\begin{aligned}
    {[Q(\sqrt{2}, \sqrt{5}, \sqrt{7}, \sqrt{11}): \mathbb{Q}] } & =[Q(\sqrt{2}, \sqrt{5}, \sqrt{7}, \sqrt{11}): Q(\sqrt{2}, \sqrt{5}, \sqrt{7})] \cdot[\mathbb{Q}(\sqrt{2}, \sqrt{5}, \sqrt{7}): \mathbb{Q}(\sqrt{2}, \sqrt{5})] \\
& \cdot[\mathbb{Q}(\sqrt{2}, \sqrt{5}): \mathbb{Q}(\sqrt{2})] \cdot[\mathbb{Q}(\sqrt{2}): \mathbb{Q}] \\
& =2 \cdot 2 \cdot 2 \cdot 2 \\
& =16
\end{aligned}
$$
Here, we note that $p(x)$ is of degree 5 over $\mathbb{Q}(\sqrt{2}, \sqrt{5}, \sqrt{7}, \sqrt{11})$. If $a$ is root of $p(x)$, then
$$
[Q(\sqrt{2}, \sqrt{5}, \sqrt{7}, \sqrt{11}, a): \mathbb{Q}]=[Q(\sqrt{2}, \sqrt{5}, \sqrt{7}, \sqrt{11}): Q(\sqrt{2}, \sqrt{5}, \sqrt{7}, \sqrt{11})] \cdot 15
$$
and $[Q(\sqrt{2}, \sqrt{5}, \sqrt{7}, \sqrt{11}): Q(\sqrt{2}, \sqrt{5}, \sqrt{7}, \sqrt{11})] \leq 5$. We get equality if $p(x)$ is irreducible over $Q(\sqrt{2}, \sqrt{5}, \sqrt{7}, \sqrt{11})$. This gives
$$
[Q(\sqrt{2}, \sqrt{5}, \sqrt{7}, \sqrt{11}, a): \mathbb{Q}] \leq 16 \cdot 5=80
$$
-/

theorem Herstein_exercise_5_4_3 {a : ℂ} {p : ℂ → ℂ}
  (hp : p = λ (x : ℂ) => x^5 + sqrt 2 * x^3 + sqrt 5 * x^2 + sqrt 7 * x + sqrt 11)
  (ha : p a = 0) :
  ∃ q : Polynomial ℂ, q ≠ 0 ∧ q.degree ≤ 80 ∧ a ∈ q.roots ∧
  ∀ n : q.support, ∃ a b : ℤ, q.coeff n = a / b := by
  have ha_root : is_root_of_p a := by unfold is_root_of_p; rw [hp] at ha; exact ha
  have ha_int := a_integral_over_Q ha_root

  -- Use minimal polynomial over ℚ mapped to ℂ
  let m := minpoly ℚ a
  let q := m.map (algebraMap ℚ ℂ)
  use q

  refine ⟨?hne, ?hdeg, ?hroot, ?hcoeff⟩

  case hne =>
    simp only [ne_eq, q, Polynomial.map_eq_zero_iff (algebraMap ℚ ℂ).injective]
    exact minpoly.ne_zero ha_int

  case hdeg =>
    /-
    ================================================================================
    PROOF OVERVIEW:
    We show deg(minpoly ℚ a) ≤ 80 using the tower law for field extensions.

    Key facts:
    - K = ℚ(√2, √5, √7, √11) has [K:ℚ] ≤ 16 (four independent quadratic extensions)
    - a satisfies the degree-5 polynomial p_K over K, so [K(a):K] ≤ 5
    - By tower law: [K(a):ℚ] = [K(a):K] · [K:ℚ] ≤ 5 · 16 = 80
    - Since natDegree(minpoly ℚ a) = [ℚ(a):ℚ] ≤ [K(a):ℚ], we have deg ≤ 80
    ================================================================================
    -/

    -- Step 1: q.degree = m.degree since mapping preserves degree for field homomorphisms
    simp only [q, Polynomial.degree_map]

    -- Step 2: Convert the goal to natDegree ≤ 80
    rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero ha_int)]

    -- Step 2.1: Now the goal is (m.natDegree : WithBot ℕ) ≤ 80
    norm_cast

    -- Step 3: Use the finrank bound directly
    -- natDegree(minpoly ℚ a) = finrank ℚ ℚ(a) ≤ finrank ℚ K(a) ≤ 16 * 5 = 80

    -- Step 3.1: Define the simple adjoin of a over ℚ in ℂ
    let Qa : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {a}

    -- Step 3.2: finrank ℚ Qa = natDegree(minpoly ℚ a)
    have hfinrank : Module.finrank ℚ Qa = (minpoly ℚ a).natDegree :=
      IntermediateField.adjoin.finrank ha_int

    -- Step 3.3: a satisfies p_K which is monic of degree 5
    have ha_p_K : Polynomial.aeval a (p_K.map (algebraMap K ℂ)) = 0 := by
      rw [p_K_map_eq]
      unfold p_C is_root_of_p at *
      simp only [Polynomial.aeval_def, eval₂_add, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C]
      exact ha_root

    -- Step 3.4: p_K.map has degree 5
    -- We use the fact that p_K is monic with natDegree 5 (it maps to p_C which is monic of degree 5)
    have hp_K_deg : p_K.degree = 5 := by
      -- p_K maps to p_C under the algebra map, and mapping preserves degree
      have heq := p_K_map_eq
      -- p_C has degree 5 - we compute this directly from its structure
      -- p_C = X^5 + √2·X³ + √5·X² + √7·X + √11
      -- First establish the degree of the polynomial without the constant term
      have hd53 : (X^5 + C (Real.sqrt 2 : ℂ) * X^3 : Polynomial ℂ).degree = 5 := by
        rw [degree_add_eq_left_of_degree_lt]
        · simp only [degree_X_pow]; norm_cast
        · calc (C (Real.sqrt 2 : ℂ) * X^3 : Polynomial ℂ).degree
              ≤ (C (Real.sqrt 2 : ℂ)).degree + (X^3).degree := degree_mul_le _ _
            _ ≤ 0 + 3 := add_le_add degree_C_le (le_of_eq (degree_X_pow 3))
            _ = (3 : ℕ) := by ring
            _ < (5 : ℕ) := by norm_num
            _ = (X^5 : Polynomial ℂ).degree := (degree_X_pow 5).symm
      have hd532 : (X^5 + C (Real.sqrt 2 : ℂ) * X^3 + C (Real.sqrt 5 : ℂ) * X^2 : Polynomial ℂ).degree = 5 := by
        rw [degree_add_eq_left_of_degree_lt]
        · exact hd53
        · calc (C (Real.sqrt 5 : ℂ) * X^2 : Polynomial ℂ).degree
              ≤ (C (Real.sqrt 5 : ℂ)).degree + (X^2).degree := degree_mul_le _ _
            _ ≤ 0 + 2 := add_le_add degree_C_le (le_of_eq (degree_X_pow 2))
            _ = (2 : ℕ) := by ring
            _ < (5 : ℕ) := by norm_num
            _ = (X^5 + C (Real.sqrt 2 : ℂ) * X^3 : Polynomial ℂ).degree := hd53.symm
      have hd5321 : (X^5 + C (Real.sqrt 2 : ℂ) * X^3 + C (Real.sqrt 5 : ℂ) * X^2 +
                    C (Real.sqrt 7 : ℂ) * X : Polynomial ℂ).degree = 5 := by
        rw [degree_add_eq_left_of_degree_lt]
        · exact hd532
        · calc (C (Real.sqrt 7 : ℂ) * X : Polynomial ℂ).degree
              ≤ (C (Real.sqrt 7 : ℂ)).degree + X.degree := degree_mul_le _ _
            _ ≤ 0 + 1 := add_le_add degree_C_le degree_X_le
            _ = (1 : ℕ) := by ring
            _ < (5 : ℕ) := by norm_num
            _ = (X^5 + C (Real.sqrt 2 : ℂ) * X^3 + C (Real.sqrt 5 : ℂ) * X^2 : Polynomial ℂ).degree := hd532.symm
      have hp_C_deg : p_C.degree = 5 := by
        unfold p_C
        rw [degree_add_eq_left_of_degree_lt]
        · exact hd5321
        · calc (C (Real.sqrt 11 : ℂ) : Polynomial ℂ).degree ≤ 0 := degree_C_le
            _ < (5 : ℕ) := by norm_num
            _ = (X^5 + C (Real.sqrt 2 : ℂ) * X^3 + C (Real.sqrt 5 : ℂ) * X^2 +
                 C (Real.sqrt 7 : ℂ) * X : Polynomial ℂ).degree := hd5321.symm
      rw [← Polynomial.degree_map (f := algebraMap K ℂ), heq, hp_C_deg]

    have hp_K_map_deg : (p_K.map (algebraMap K ℂ)).degree = 5 := by
      rw [Polynomial.degree_map (f := algebraMap K ℂ), hp_K_deg]

    -- Step 3.5: Get minpoly K a degree bound
    -- We need to use minpoly.min with p_K (not p_K.map)
    have hdeg_K : (minpoly K a).degree ≤ 5 := by
      have hne : p_K ≠ 0 := fun h => by
        have hmon : p_K.Monic := p_K_monic
        rw [h] at hmon
        exact Polynomial.not_monic_zero hmon
      -- a is a root of p_K when evaluated via the K-algebra structure on ℂ
      -- We need aeval K a p_K = 0
      have ha_p_K_K : Polynomial.aeval (R := K) a p_K = 0 := by
        -- aeval K a p_K = eval₂ (algebraMap K ℂ) a p_K = (p_K.map (algebraMap K ℂ)).eval a
        rw [Polynomial.aeval_def, ← Polynomial.eval_map, p_K_map_eq]
        unfold p_C is_root_of_p at *
        simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
                   Polynomial.eval_mul, Polynomial.eval_C]
        exact ha_root
      have h := minpoly.min K a p_K_monic ha_p_K_K
      calc (minpoly K a).degree ≤ p_K.degree := h
        _ = 5 := by rw [← hp_K_map_deg, Polynomial.degree_map]

    have hnat_K_5 : (minpoly K a).natDegree ≤ 5 :=
      Polynomial.natDegree_le_of_degree_le hdeg_K

    -- Step 4: K is finite dimensional over ℚ
    haveI hK_fin : FiniteDimensional ℚ K := by
      apply IntermediateField.finiteDimensional_adjoin
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact isIntegral_sqrt_nat 2
      · exact isIntegral_sqrt_nat 5
      · exact isIntegral_sqrt_nat 7
      · exact isIntegral_sqrt_nat 11

    -- Step 5: K(a) is finite dimensional over K
    let Ka : IntermediateField K ℂ := IntermediateField.adjoin K {a}
    haveI hKa_fin : FiniteDimensional K Ka := by
      apply IntermediateField.finiteDimensional_adjoin
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      rw [hx]; exact a_integral_over_K ha_root

    -- Step 6: finrank K Ka ≤ 5
    have hKa_rank : Module.finrank K Ka ≤ 5 := by
      rw [IntermediateField.adjoin.finrank (a_integral_over_K ha_root)]
      exact hnat_K_5

    -- Step 7: Qa is finite dimensional (since a is integral over ℚ)
    haveI hQa_fin : FiniteDimensional ℚ Qa := by
      apply IntermediateField.finiteDimensional_adjoin
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      rw [hx]; exact ha_int

    -- Step 8: Use the tower structure via restrictScalars
    -- K(a) viewed over ℚ
    let Ka_Q := IntermediateField.restrictScalars ℚ Ka

    -- Step 9: Qa ⊆ Ka_Q
    have hQa_le : Qa ≤ Ka_Q := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.mem_adjoin_simple_self K a

    -- Step 10: Final bound using the tower law
    -- natDegree(minpoly ℚ a) = finrank ℚ Qa ≤ finrank ℚ Ka ≤ finrank ℚ K * finrank K Ka ≤ 16 * 5 = 80

    -- Step 10.1: Set up the scalar tower ℚ → K → Ka
    -- This is needed for the tower law and finiteness transitivity
    haveI hScalarTower : IsScalarTower ℚ K Ka := IntermediateField.isScalarTower Ka

    -- Step 10.2: Ka is finite dimensional over ℚ (by transitivity through K)
    haveI hKa_Q_fin : FiniteDimensional ℚ Ka := Module.Finite.trans K Ka

    -- Step 10.3: Compute finrank ℚ Ka = finrank ℚ K * finrank K Ka using the tower law
    have hKa_finrank : Module.finrank ℚ K * Module.finrank K Ka = Module.finrank ℚ Ka :=
      Module.finrank_mul_finrank ℚ K Ka

    -- Step 10.4: Show finrank ℚ K ≤ 16
    -- K = ℚ(√2, √5, √7, √11) is contained in a tower of quadratic extensions
    -- Each √p has minpoly X² - p of degree 2, so finrank doubles at each step
    -- The bound 16 = 2^4 comes from adjoining 4 elements of degree ≤ 2

    -- Helper: minpoly of √k over ℚ has degree ≤ 2
    have minpoly_sqrt_deg : ∀ k : ℕ, (minpoly ℚ (Real.sqrt k : ℂ)).natDegree ≤ 2 := by
      intro k
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hp : Polynomial.aeval (R := ℚ) (Real.sqrt k : ℂ) (X^2 - C (k : ℚ)) = 0 := by
        simp only [Polynomial.aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
        rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt hk]
        simp only [sub_eq_zero]; symm; exact_mod_cast rfl
      have hmonic : (X^2 - C (k : ℚ)).Monic := monic_X_pow_sub_C (k : ℚ) (by norm_num : (2 : ℕ) ≠ 0)
      have hdeg_le := minpoly.min ℚ (Real.sqrt k : ℂ) hmonic hp
      have hdeg_p : (X^2 - C (k : ℚ)).degree = 2 := degree_X_pow_sub_C (by norm_num : (0 : ℕ) < 2) (k : ℚ)
      rw [hdeg_p] at hdeg_le
      exact Polynomial.natDegree_le_of_degree_le hdeg_le

    -- K ⊆ ℚ(√2)(√5)(√7)(√11) which has finrank ≤ 2^4 = 16 by the tower law
    -- For simplicity, we use the fact that K = adjoin ℚ {√2, √5, √7, √11}
    -- and bound finrank by the product of individual minimal polynomial degrees

    -- Using IntermediateField.adjoin_le_adjoin for S ⊆ S' → adjoin S ≤ adjoin S'
    -- and the fact that K is already the full adjoin

    -- For a rigorous bound, we use: K is generated by 4 elements, each with degree ≤ 2
    -- A spanning set for K over ℚ consists of products of powers of generators
    -- {√2^i * √5^j * √7^k * √11^l : i,j,k,l ∈ {0,1}} has 16 elements
    -- This implies finrank ℚ K ≤ 16

    -- We prove this using the fact that finrank of adjoin(S) ≤ ∏_{x∈S} deg(minpoly x)
    -- when elements are integral. This is a consequence of the tower law.

    have hK_finrank : Module.finrank ℚ K ≤ 16 := by
      /-
      ================================================================================
      PROOF THAT [K : ℚ] ≤ 16 where K = ℚ(√2, √5, √7, √11)
      ================================================================================
      We prove this by constructing the tower of field extensions:
        ℚ ⊆ ℚ(√2) ⊆ ℚ(√2,√5) ⊆ ℚ(√2,√5,√7) ⊆ ℚ(√2,√5,√7,√11) = K
      and applying the tower law at each step.

      Step 1: Define intermediate fields K₁ = ℚ(√2), K₂ = ℚ(√2,√5), K₃ = ℚ(√2,√5,√7)
      Step 2: Show each √n is integral over the previous field
      Step 3: Show each extension has degree ≤ 2 (since √n satisfies X² - n)
      Step 4: Apply tower law: [K:ℚ] = [K:K₃]·[K₃:K₂]·[K₂:K₁]·[K₁:ℚ] ≤ 2·2·2·2 = 16
      ================================================================================
      -/

      -- Step 1: Define the tower of intermediate fields
      -- K₁ = ℚ(√2)
      let K1 : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {(Real.sqrt 2 : ℂ)}
      -- K₂ = ℚ(√2, √5)
      let K2 : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ)}
      -- K₃ = ℚ(√2, √5, √7)
      let K3 : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ
        {(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ), (Real.sqrt 7 : ℂ)}

      -- Step 2: Establish finite dimensionality for all intermediate fields
      haveI K1_finite : FiniteDimensional ℚ K1 := by
        apply IntermediateField.finiteDimensional_adjoin
        intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; exact isIntegral_sqrt_nat 2
      haveI K2_finite : FiniteDimensional ℚ K2 := by
        apply IntermediateField.finiteDimensional_adjoin
        intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl; exact isIntegral_sqrt_nat 2; exact isIntegral_sqrt_nat 5
      haveI K3_finite : FiniteDimensional ℚ K3 := by
        apply IntermediateField.finiteDimensional_adjoin
        intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl; exact isIntegral_sqrt_nat 2; exact isIntegral_sqrt_nat 5; exact isIntegral_sqrt_nat 7

      -- Step 3: Show √5 is integral over K₁, √7 is integral over K₂, √11 is integral over K₃
      have h_int_5_K1 : IsIntegral K1 (Real.sqrt 5 : ℂ) := (isIntegral_sqrt_nat 5).tower_top
      have h_int_7_K2 : IsIntegral K2 (Real.sqrt 7 : ℂ) := (isIntegral_sqrt_nat 7).tower_top
      have h_int_11_K3 : IsIntegral K3 (Real.sqrt 11 : ℂ) := (isIntegral_sqrt_nat 11).tower_top

      -- Step 4: Finite dimensionality of each extension
      -- K1(√5) is the simple adjoin of √5 over K1
      let K1_sqrt5 : IntermediateField K1 ℂ := IntermediateField.adjoin K1 {(Real.sqrt 5 : ℂ)}
      let K2_sqrt7 : IntermediateField K2 ℂ := IntermediateField.adjoin K2 {(Real.sqrt 7 : ℂ)}
      let K3_sqrt11 : IntermediateField K3 ℂ := IntermediateField.adjoin K3 {(Real.sqrt 11 : ℂ)}
      haveI K1_sqrt5_finite : FiniteDimensional K1 K1_sqrt5 := by
        apply IntermediateField.finiteDimensional_adjoin
        intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; exact h_int_5_K1
      haveI K2_sqrt7_finite : FiniteDimensional K2 K2_sqrt7 := by
        apply IntermediateField.finiteDimensional_adjoin
        intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; exact h_int_7_K2
      haveI K3_sqrt11_finite : FiniteDimensional K3 K3_sqrt11 := by
        apply IntermediateField.finiteDimensional_adjoin
        intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; exact h_int_11_K3

      -- Step 5: Key relations using adjoin_simple_adjoin_simple and adjoin_adjoin_left
      -- Step 5.1: K₂ = restrictScalars ℚ K1_sqrt5
      have K2_eq : K2 = IntermediateField.restrictScalars ℚ K1_sqrt5 := by
        exact (IntermediateField.adjoin_simple_adjoin_simple ℚ _ _).symm
      -- Step 5.2: K₃ = restrictScalars ℚ K2_sqrt7
      have K3_eq : K3 = IntermediateField.restrictScalars ℚ K2_sqrt7 := by
        have h := IntermediateField.adjoin_adjoin_left ℚ
          ({(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ)} : Set ℂ) {(Real.sqrt 7 : ℂ)}
        have hset : ({(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ)} ∪ {(Real.sqrt 7 : ℂ)} : Set ℂ) =
                    {(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ), (Real.sqrt 7 : ℂ)} := by
          ext x; simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rw [hset] at h
        exact h.symm
      -- Step 5.3: K = restrictScalars ℚ K3_sqrt11
      have K_eq : K = IntermediateField.restrictScalars ℚ K3_sqrt11 := by
        have h := IntermediateField.adjoin_adjoin_left ℚ
          ({(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ), (Real.sqrt 7 : ℂ)} : Set ℂ) {(Real.sqrt 11 : ℂ)}
        have hset : ({(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ), (Real.sqrt 7 : ℂ)} ∪ {(Real.sqrt 11 : ℂ)} : Set ℂ) =
                    {(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ), (Real.sqrt 7 : ℂ), (Real.sqrt 11 : ℂ)} := by
          ext x; simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rw [hset] at h
        exact h.symm

      -- Step 6: Prove finrank bounds for each step using minpoly degree bounds
      -- Step 6.1: [K₁ : ℚ] ≤ 2
      -- K1 = ℚ⟮√2⟯ (simple adjoin), so finrank = natDegree(minpoly ℚ √2) ≤ 2
      have K1_finrank_le : Module.finrank ℚ K1 ≤ 2 := by
        -- K1 is definitionally ℚ⟮√2⟯, so we just apply adjoin.finrank
        calc Module.finrank ℚ K1
            = (minpoly ℚ (Real.sqrt 2 : ℂ)).natDegree := IntermediateField.adjoin.finrank (isIntegral_sqrt_nat 2)
          _ ≤ 2 := minpoly_sqrt_deg 2
      -- Step 6.2: [K₁(√5) : K₁] ≤ 2
      have K1_K2_finrank_le : Module.finrank K1 K1_sqrt5 ≤ 2 := by
        rw [IntermediateField.adjoin.finrank h_int_5_K1]
        -- minpoly K₁ √5 divides X² - 5, so has degree ≤ 2
        have hp : Polynomial.aeval (R := K1) (Real.sqrt 5 : ℂ) (X^2 - C (5 : K1)) = 0 := by
          simp only [Polynomial.aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
                     IntermediateField.algebraMap_apply]
          rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
          simp only [sub_eq_zero]; norm_cast
        have hmonic : (X^2 - C (5 : K1)).Monic := monic_X_pow_sub_C _ (by norm_num)
        have hdeg_le := minpoly.min K1 (Real.sqrt 5 : ℂ) hmonic hp
        have hdeg_p : (X^2 - C (5 : K1)).degree = 2 := degree_X_pow_sub_C (by norm_num) _
        rw [hdeg_p] at hdeg_le; exact Polynomial.natDegree_le_of_degree_le hdeg_le
      -- Step 6.3: [K₂(√7) : K₂] ≤ 2
      have K2_K3_finrank_le : Module.finrank K2 K2_sqrt7 ≤ 2 := by
        rw [IntermediateField.adjoin.finrank h_int_7_K2]
        have hp : Polynomial.aeval (R := K2) (Real.sqrt 7 : ℂ) (X^2 - C (7 : K2)) = 0 := by
          simp only [Polynomial.aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
                     IntermediateField.algebraMap_apply]
          rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 7)]
          simp only [sub_eq_zero]; norm_cast
        have hmonic : (X^2 - C (7 : K2)).Monic := monic_X_pow_sub_C _ (by norm_num)
        have hdeg_le := minpoly.min K2 (Real.sqrt 7 : ℂ) hmonic hp
        have hdeg_p : (X^2 - C (7 : K2)).degree = 2 := degree_X_pow_sub_C (by norm_num) _
        rw [hdeg_p] at hdeg_le; exact Polynomial.natDegree_le_of_degree_le hdeg_le
      -- Step 6.4: [K₃(√11) : K₃] ≤ 2
      have K3_K_finrank_le : Module.finrank K3 K3_sqrt11 ≤ 2 := by
        rw [IntermediateField.adjoin.finrank h_int_11_K3]
        have hp : Polynomial.aeval (R := K3) (Real.sqrt 11 : ℂ) (X^2 - C (11 : K3)) = 0 := by
          simp only [Polynomial.aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
                     IntermediateField.algebraMap_apply]
          rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 11)]
          simp only [sub_eq_zero]; norm_cast
        have hmonic : (X^2 - C (11 : K3)).Monic := monic_X_pow_sub_C _ (by norm_num)
        have hdeg_le := minpoly.min K3 (Real.sqrt 11 : ℂ) hmonic hp
        have hdeg_p : (X^2 - C (11 : K3)).degree = 2 := degree_X_pow_sub_C (by norm_num) _
        rw [hdeg_p] at hdeg_le; exact Polynomial.natDegree_le_of_degree_le hdeg_le

      -- Step 7: Apply tower law to compute cumulative bounds
      -- Step 7.1: [K₂ : ℚ] ≤ 4
      have K2_finrank_le : Module.finrank ℚ K2 ≤ 4 := by
        rw [K2_eq]
        have htower := Module.finrank_mul_finrank ℚ K1 K1_sqrt5
        calc Module.finrank ℚ (IntermediateField.restrictScalars ℚ K1_sqrt5)
            = Module.finrank ℚ K1_sqrt5 := rfl
          _ = Module.finrank ℚ K1 * Module.finrank K1 K1_sqrt5 := htower.symm
          _ ≤ 2 * 2 := Nat.mul_le_mul K1_finrank_le K1_K2_finrank_le
          _ = 4 := by norm_num
      -- Step 7.2: [K₃ : ℚ] ≤ 8
      have K3_finrank_le : Module.finrank ℚ K3 ≤ 8 := by
        rw [K3_eq]
        have htower := Module.finrank_mul_finrank ℚ K2 K2_sqrt7
        calc Module.finrank ℚ (IntermediateField.restrictScalars ℚ K2_sqrt7)
            = Module.finrank ℚ K2_sqrt7 := rfl
          _ = Module.finrank ℚ K2 * Module.finrank K2 K2_sqrt7 := htower.symm
          _ ≤ 4 * 2 := Nat.mul_le_mul K2_finrank_le K2_K3_finrank_le
          _ = 8 := by norm_num
      -- Step 7.3: [K : ℚ] ≤ 16 (final result)
      rw [K_eq]
      have htower := Module.finrank_mul_finrank ℚ K3 K3_sqrt11
      calc Module.finrank ℚ (IntermediateField.restrictScalars ℚ K3_sqrt11)
          = Module.finrank ℚ K3_sqrt11 := rfl
        _ = Module.finrank ℚ K3 * Module.finrank K3 K3_sqrt11 := htower.symm
        _ ≤ 8 * 2 := Nat.mul_le_mul K3_finrank_le K3_K_finrank_le
        _ = 16 := by norm_num

    -- Step 10.5: Compute the bound
    have hKa_bound : Module.finrank ℚ Ka ≤ 80 := by
      calc Module.finrank ℚ Ka
          = Module.finrank ℚ K * Module.finrank K Ka := hKa_finrank.symm
        _ ≤ 16 * 5 := Nat.mul_le_mul hK_finrank hKa_rank
        _ = 80 := by norm_num

    -- Step 10.6: Use inclusion Qa ≤ Ka (when restricted to ℚ-algebra)
    -- to get finrank ℚ Qa ≤ finrank ℚ Ka

    -- First, show Qa ≤ Ka when both are viewed as IntermediateField ℚ ℂ
    -- Qa = ℚ(a), Ka contains a (since Ka = K(a))

    -- The inclusion Qa → Ka gives finrank ℚ Qa ≤ finrank ℚ Ka
    have hQa_le_Ka : Module.finrank ℚ Qa ≤ Module.finrank ℚ Ka := by
      -- Qa ≤ Ka_Q = Ka.restrictScalars ℚ (which has the same carrier as Ka)
      -- The inclusion map is injective, so finrank is bounded

      -- Ka_Q = Ka.restrictScalars ℚ has the same ℚ-module structure as Ka
      -- So FiniteDimensional ℚ Ka implies FiniteDimensional ℚ Ka_Q
      haveI hKa_Q_fin' : FiniteDimensional ℚ Ka_Q := hKa_Q_fin

      -- Use LinearMap.finrank_le_finrank_of_injective
      let incl := IntermediateField.inclusion hQa_le
      have hinj : Function.Injective incl.toLinearMap := by
        intro x y hxy
        have h1 : ((incl x : Ka_Q) : ℂ) = ((incl y : Ka_Q) : ℂ) := congrArg Subtype.val hxy
        exact Subtype.ext h1

      -- Ka_Q = Ka.restrictScalars ℚ
      -- As a ℚ-vector space, Ka_Q is isomorphic to Ka
      -- so finrank ℚ Ka_Q = finrank ℚ Ka
      have hKa_Q_eq : Module.finrank ℚ Ka_Q = Module.finrank ℚ Ka := rfl

      calc Module.finrank ℚ Qa
          ≤ Module.finrank ℚ Ka_Q := LinearMap.finrank_le_finrank_of_injective hinj
        _ = Module.finrank ℚ Ka := hKa_Q_eq

    -- Final calculation
    calc (minpoly ℚ a).natDegree
        = Module.finrank ℚ Qa := hfinrank.symm
      _ ≤ Module.finrank ℚ Ka := hQa_le_Ka
      _ ≤ 80 := hKa_bound

  case hroot =>
    rw [Polynomial.mem_roots']
    constructor
    · simp only [ne_eq, q, Polynomial.map_eq_zero_iff (algebraMap ℚ ℂ).injective]
      exact minpoly.ne_zero ha_int
    · simp only [q, IsRoot, eval_map_algebraMap]
      exact minpoly.aeval ℚ a

  case hcoeff =>
    intro n
    have h : q.coeff n.val = (algebraMap ℚ ℂ) (m.coeff n.val) := Polynomial.coeff_map _ _
    use (m.coeff n.val).num, (m.coeff n.val).den
    rw [h]; exact rat_cast_eq_int_div _




/-
The original formalization `Herstein_exercise_5_4_3` is faithful, but the version
below (`_more_literal`) is a more literal translation of the informal statement.
The two are logically EQUIVALENT, but differ in encoding choices:

  1. Hypothesis: The original introduces an auxiliary function `p` with
     `hp : p = λ x => x^5 + √2*x³ + √5*x² + √7*x + √11` and `ha : p a = 0`.
     The more literal version directly states
     `ha : a^5 + √2*a³ + √5*a² + √7*a + √11 = 0`.
     The latter mirrors the informal statement "if a satisfies p(a) = 0" without
     the indirection of naming p as a separate hypothesis.

  2. Conclusion: The original existentially quantifies over `Polynomial ℂ` and
     then asserts all coefficients have the form a/b for integers a, b : ℤ
     (encoding "rational coefficients" by hand). The more literal version
     existentially quantifies over `Polynomial ℚ` directly, which is the
     idiomatic Lean/Mathlib way to say "a polynomial with rational coefficients."
     The two are equivalent because a complex polynomial with all-rational
     coefficients is exactly the image of a rational polynomial under the
     algebra map ℚ → ℂ.

  3. Root condition: The original uses `a ∈ q.roots`; the more literal version
     uses `Polynomial.aeval a q = 0`. These are equivalent (for nonzero q),
     but `aeval` is the standard Mathlib idiom for "a is a root of q."

  4. Degree: The original uses `q.degree ≤ 80` (in `WithBot ℕ`); the more
     literal version uses `q.natDegree ≤ 80` (in `ℕ`). Equivalent for nonzero
     polynomials. The `natDegree` form is simpler and avoids `WithBot` coercions.

The more literal formalization is preferred because:
  - It directly encodes the hypothesis as stated, without auxiliary definitions.
  - It uses `Polynomial ℚ` to express "rational polynomial" rather than
    re-encoding rationality via an integer-quotient condition on coefficients.
  - It uses standard Mathlib idioms (`aeval`, `natDegree`) throughout.

================================================================================
PROOF OVERVIEW:

We show: there exists a nonzero rational polynomial q of degree ≤ 80 such that
aeval a q = 0 (i.e., a is algebraic over ℚ of degree at most 80).

Strategy:
  - Witness: q = minpoly ℚ a (the minimal polynomial of a over ℚ).
  - Nonzero: minpoly is always nonzero for integral elements.
  - Root: aeval a (minpoly ℚ a) = 0 by definition of minpoly.
  - Degree bound: We show natDegree(minpoly ℚ a) ≤ 80 via the tower law:
      [ℚ(a) : ℚ] ≤ [K(a) : ℚ] = [K : ℚ] · [K(a) : K] ≤ 16 · 5 = 80,
    where K = ℚ(√2, √5, √7, √11).

The proof proceeds in the following steps:
  Step 1: Establish that a is integral over ℚ (using helper lemmas).
  Step 2: Choose the witness (minpoly ℚ a) and discharge nonzero + root goals.
  Step 3: Show deg(p_K) = 5, where p_K is the polynomial over K that a satisfies.
  Step 4: Show natDegree(minpoly K a) ≤ 5 (since minpoly divides p_K).
  Step 5: Show K is finite-dimensional over ℚ.
  Step 6: Show natDegree(minpoly ℚ √k) ≤ 2 for any natural k.
  Step 7: Build the tower ℚ ⊆ K₁ ⊆ K₂ ⊆ K₃ ⊆ K and bound each step's degree.
  Step 8: Combine to get [K : ℚ] ≤ 16.
  Step 9: Build K(a) and show [K(a) : K] ≤ 5.
  Step 10: Use the inclusion ℚ(a) ⊆ K(a) and tower law to get the final bound.
================================================================================
-/
theorem Herstein_exercise_5_4_3_more_literal {a : ℂ}
    (ha : a ^ 5 + (Real.sqrt 2 : ℂ) * a ^ 3 + (Real.sqrt 5 : ℂ) * a ^ 2 +
      (Real.sqrt 7 : ℂ) * a + (Real.sqrt 11 : ℂ) = 0) :
    ∃ q : Polynomial ℚ, q ≠ 0 ∧ q.natDegree ≤ 80 ∧
      Polynomial.aeval a q = 0 := by
  -- Step 1: Establish that a is integral over ℚ.
  -- Step 1.1: Rewrite the hypothesis as `is_root_of_p a` (just unfolding the definition).
  have ha_root : is_root_of_p a := ha
  -- Step 1.2: Use the pre-proved lemma `a_integral_over_Q` which shows a is integral over ℚ
  -- via the tower ℚ → K → ℂ (a is integral over K since it's a root of the monic p_K,
  -- and K is integral over ℚ, so by transitivity a is integral over ℚ).
  have ha_int := a_integral_over_Q ha_root
  -- Step 2: Choose the witness and discharge two of the three conjuncts.
  -- Step 2.1: Our witness is `minpoly ℚ a`, the minimal polynomial of a over ℚ.
  -- Step 2.2: `minpoly.ne_zero ha_int` proves it is nonzero (since a is integral).
  -- Step 2.3: `minpoly.aeval ℚ a` proves aeval a (minpoly ℚ a) = 0 (by definition of minpoly).
  -- Step 2.4: The remaining goal is `(minpoly ℚ a).natDegree ≤ 80`.
  refine ⟨minpoly ℚ a, minpoly.ne_zero ha_int, ?_, minpoly.aeval ℚ a⟩
  -- Step 2.5: Define ℚ(a) as the simple adjunction of a over ℚ in ℂ.
  let Qa : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {a}
  -- Step 2.6: The key identity: [ℚ(a) : ℚ] = natDegree(minpoly ℚ a).
  -- This converts the degree bound into a finrank bound.
  have hfinrank : Module.finrank ℚ Qa = (minpoly ℚ a).natDegree :=
    IntermediateField.adjoin.finrank ha_int
  -- Step 3: Show deg(p_K) = 5.
  -- p_K is the polynomial X⁵ + √2·X³ + √5·X² + √7·X + √11 defined over K.
  -- Its degree equals 5 because the leading term X⁵ dominates all lower-degree terms.
  -- We prove this by mapping p_K to ℂ (where it equals p_C) and computing the degree there.
  have hp_K_deg : p_K.degree = 5 := by
    -- Step 3.1: degree(p_K) = degree(p_K.map (algebraMap K ℂ)) since algebraMap is injective.
    rw [← Polynomial.degree_map (f := algebraMap K ℂ), p_K_map_eq]
    -- Step 3.2: Now we compute degree(p_C) = 5 by showing each lower-degree term
    -- has degree strictly less than the leading X⁵ term.
    unfold p_C
    -- Step 3.3: degree(X⁵ + √2·X³) = 5 since deg(√2·X³) ≤ 3 < 5.
    have hd53 : (X ^ 5 + C (Real.sqrt 2 : ℂ) * X ^ 3 : Polynomial ℂ).degree = 5 := by
      rw [degree_add_eq_left_of_degree_lt]
      · simp only [degree_X_pow]; norm_cast
      · calc (C (Real.sqrt 2 : ℂ) * X ^ 3 : Polynomial ℂ).degree
            ≤ (C (Real.sqrt 2 : ℂ)).degree + (X ^ 3).degree := degree_mul_le _ _
          _ ≤ 0 + 3 := add_le_add degree_C_le (le_of_eq (degree_X_pow 3))
          _ = (3 : ℕ) := by ring
          _ < (5 : ℕ) := by norm_num
          _ = (X ^ 5 : Polynomial ℂ).degree := (degree_X_pow 5).symm
    -- Step 3.4: degree(X⁵ + √2·X³ + √5·X²) = 5 since deg(√5·X²) ≤ 2 < 5.
    have hd532 : (X ^ 5 + C (Real.sqrt 2 : ℂ) * X ^ 3 + C (Real.sqrt 5 : ℂ) * X ^ 2 : Polynomial ℂ).degree = 5 := by
      rw [degree_add_eq_left_of_degree_lt]
      · exact hd53
      · calc (C (Real.sqrt 5 : ℂ) * X ^ 2 : Polynomial ℂ).degree
            ≤ (C (Real.sqrt 5 : ℂ)).degree + (X ^ 2).degree := degree_mul_le _ _
          _ ≤ 0 + 2 := add_le_add degree_C_le (le_of_eq (degree_X_pow 2))
          _ = (2 : ℕ) := by ring
          _ < (5 : ℕ) := by norm_num
          _ = (X ^ 5 + C (Real.sqrt 2 : ℂ) * X ^ 3 : Polynomial ℂ).degree := hd53.symm
    -- Step 3.5: degree(X⁵ + √2·X³ + √5·X² + √7·X) = 5 since deg(√7·X) ≤ 1 < 5.
    have hd5321 : (X ^ 5 + C (Real.sqrt 2 : ℂ) * X ^ 3 + C (Real.sqrt 5 : ℂ) * X ^ 2 +
                  C (Real.sqrt 7 : ℂ) * X : Polynomial ℂ).degree = 5 := by
      rw [degree_add_eq_left_of_degree_lt]
      · exact hd532
      · calc (C (Real.sqrt 7 : ℂ) * X : Polynomial ℂ).degree
            ≤ (C (Real.sqrt 7 : ℂ)).degree + X.degree := degree_mul_le _ _
          _ ≤ 0 + 1 := add_le_add degree_C_le degree_X_le
          _ = (1 : ℕ) := by ring
          _ < (5 : ℕ) := by norm_num
          _ = (X ^ 5 + C (Real.sqrt 2 : ℂ) * X ^ 3 + C (Real.sqrt 5 : ℂ) * X ^ 2 : Polynomial ℂ).degree := hd532.symm
    -- Step 3.6: degree(p_C) = 5 since deg(√11) ≤ 0 < 5.
    rw [degree_add_eq_left_of_degree_lt]
    · exact hd5321
    · calc (C (Real.sqrt 11 : ℂ) : Polynomial ℂ).degree ≤ 0 := degree_C_le
        _ < (5 : ℕ) := by norm_num
        _ = (X ^ 5 + C (Real.sqrt 2 : ℂ) * X ^ 3 + C (Real.sqrt 5 : ℂ) * X ^ 2 +
             C (Real.sqrt 7 : ℂ) * X : Polynomial ℂ).degree := hd5321.symm
  -- Step 4: Show natDegree(minpoly K a) ≤ 5.
  -- Step 4.1: Show a is a root of p_K when evaluated via the K-algebra structure on ℂ.
  -- This converts the hypothesis ha (stated over ℂ) into the statement aeval_K a p_K = 0.
  have ha_p_K_K : Polynomial.aeval (R := K) a p_K = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, p_K_map_eq]
    unfold p_C is_root_of_p at *
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
               Polynomial.eval_mul, Polynomial.eval_C]
    exact ha_root
  -- Step 4.2: Since p_K is monic and a is a root, minpoly K a divides p_K.
  -- Therefore deg(minpoly K a) ≤ deg(p_K) = 5, so natDegree(minpoly K a) ≤ 5.
  have hdeg_K : (minpoly K a).natDegree ≤ 5 := by
    have h := minpoly.min K a p_K_monic ha_p_K_K
    rw [hp_K_deg] at h
    exact Polynomial.natDegree_le_of_degree_le h
  -- Step 5: Show K = ℚ(√2, √5, √7, √11) is finite-dimensional over ℚ.
  -- This follows because each generator √k is integral over ℚ (it satisfies X² - k).
  haveI hK_fin : FiniteDimensional ℚ K := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact isIntegral_sqrt_nat 2
    · exact isIntegral_sqrt_nat 5
    · exact isIntegral_sqrt_nat 7
    · exact isIntegral_sqrt_nat 11
  -- Step 6: Show natDegree(minpoly ℚ (√k : ℂ)) ≤ 2 for any natural number k.
  -- Proof: √k satisfies the monic polynomial X² - k over ℚ, so the minimal polynomial
  -- has degree at most 2 (since minpoly divides any monic polynomial with the element as root).
  have minpoly_sqrt_deg : ∀ k : ℕ, (minpoly ℚ (Real.sqrt k : ℂ)).natDegree ≤ 2 := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    -- Step 6.1: Show (√k)² - k = 0 in ℂ, i.e., √k is a root of X² - k.
    have hp : Polynomial.aeval (R := ℚ) (Real.sqrt k : ℂ) (X ^ 2 - C (k : ℚ)) = 0 := by
      simp only [Polynomial.aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt hk]
      simp only [sub_eq_zero]; symm; exact_mod_cast rfl
    -- Step 6.2: X² - k is monic (leading coefficient is 1).
    have hmonic : (X ^ 2 - C (k : ℚ)).Monic := monic_X_pow_sub_C (k : ℚ) (by norm_num : (2 : ℕ) ≠ 0)
    -- Step 6.3: minpoly divides any monic polynomial with the element as root,
    -- so deg(minpoly) ≤ deg(X² - k) = 2.
    have hdeg_le := minpoly.min ℚ (Real.sqrt k : ℂ) hmonic hp
    have hdeg_p : (X ^ 2 - C (k : ℚ)).degree = 2 := degree_X_pow_sub_C (by norm_num : (0 : ℕ) < 2) (k : ℚ)
    rw [hdeg_p] at hdeg_le
    exact Polynomial.natDegree_le_of_degree_le hdeg_le
  -- Step 7: Build the tower of intermediate fields:
  --   ℚ ⊆ K₁ = ℚ(√2) ⊆ K₂ = ℚ(√2,√5) ⊆ K₃ = ℚ(√2,√5,√7) ⊆ K = ℚ(√2,√5,√7,√11)
  -- and bound each extension degree by 2.
  -- Step 7.1: Define intermediate fields K₁, K₂, K₃.
  let K1 : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {(Real.sqrt 2 : ℂ)}
  let K2 : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ)}
  let K3 : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ
    {(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ), (Real.sqrt 7 : ℂ)}
  -- Step 7.2: Establish finite-dimensionality of each intermediate field over ℚ.
  -- (Needed for the tower law applications later.)
  haveI K1_finite : FiniteDimensional ℚ K1 := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; exact isIntegral_sqrt_nat 2
  haveI K2_finite : FiniteDimensional ℚ K2 := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl; exact isIntegral_sqrt_nat 2; exact isIntegral_sqrt_nat 5
  haveI K3_finite : FiniteDimensional ℚ K3 := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl; exact isIntegral_sqrt_nat 2; exact isIntegral_sqrt_nat 5; exact isIntegral_sqrt_nat 7
  -- Step 7.3: Show each √p is integral over the previous field in the tower.
  -- √5 is integral over K₁ (since it's integral over ℚ, hence over any extension).
  -- Similarly for √7 over K₂ and √11 over K₃.
  have h_int_5_K1 : IsIntegral K1 (Real.sqrt 5 : ℂ) := (isIntegral_sqrt_nat 5).tower_top
  have h_int_7_K2 : IsIntegral K2 (Real.sqrt 7 : ℂ) := (isIntegral_sqrt_nat 7).tower_top
  have h_int_11_K3 : IsIntegral K3 (Real.sqrt 11 : ℂ) := (isIntegral_sqrt_nat 11).tower_top
  -- Step 7.4: Define the simple extensions at each level of the tower.
  -- K₁(√5) is the adjunction of √5 over K₁, etc.
  let K1_sqrt5 : IntermediateField K1 ℂ := IntermediateField.adjoin K1 {(Real.sqrt 5 : ℂ)}
  let K2_sqrt7 : IntermediateField K2 ℂ := IntermediateField.adjoin K2 {(Real.sqrt 7 : ℂ)}
  let K3_sqrt11 : IntermediateField K3 ℂ := IntermediateField.adjoin K3 {(Real.sqrt 11 : ℂ)}
  -- Step 7.5: Establish finite-dimensionality of each simple extension.
  haveI K1_sqrt5_finite : FiniteDimensional K1 K1_sqrt5 := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; exact h_int_5_K1
  haveI K2_sqrt7_finite : FiniteDimensional K2 K2_sqrt7 := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; exact h_int_7_K2
  haveI K3_sqrt11_finite : FiniteDimensional K3 K3_sqrt11 := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; exact h_int_11_K3
  -- Step 7.6: Identify the intermediate fields via the adjoin-adjoin law.
  -- K₂ = ℚ(√2, √5) = (ℚ(√2))(√5) = K₁(√5) (as ℚ-algebras via restrictScalars).
  have K2_eq : K2 = IntermediateField.restrictScalars ℚ K1_sqrt5 :=
    (IntermediateField.adjoin_simple_adjoin_simple ℚ _ _).symm
  -- K₃ = ℚ(√2, √5, √7) = K₂(√7) (as ℚ-algebras via restrictScalars).
  have K3_eq : K3 = IntermediateField.restrictScalars ℚ K2_sqrt7 := by
    have h := IntermediateField.adjoin_adjoin_left ℚ
      ({(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ)} : Set ℂ) {(Real.sqrt 7 : ℂ)}
    have hset : ({(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ)} ∪ {(Real.sqrt 7 : ℂ)} : Set ℂ) =
                {(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ), (Real.sqrt 7 : ℂ)} := by
      ext x; simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset] at h; exact h.symm
  -- K = ℚ(√2, √5, √7, √11) = K₃(√11) (as ℚ-algebras via restrictScalars).
  have K_eq : K = IntermediateField.restrictScalars ℚ K3_sqrt11 := by
    have h := IntermediateField.adjoin_adjoin_left ℚ
      ({(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ), (Real.sqrt 7 : ℂ)} : Set ℂ) {(Real.sqrt 11 : ℂ)}
    have hset : ({(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ), (Real.sqrt 7 : ℂ)} ∪ {(Real.sqrt 11 : ℂ)} : Set ℂ) =
                {(Real.sqrt 2 : ℂ), (Real.sqrt 5 : ℂ), (Real.sqrt 7 : ℂ), (Real.sqrt 11 : ℂ)} := by
      ext x; simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset] at h; exact h.symm
  -- Step 7.7: Bound [K₁ : ℚ] ≤ 2.
  -- K₁ = ℚ(√2) is a simple extension, so [K₁:ℚ] = natDegree(minpoly ℚ √2) ≤ 2.
  have K1_finrank_le : Module.finrank ℚ K1 ≤ 2 := by
    calc Module.finrank ℚ K1
        = (minpoly ℚ (Real.sqrt 2 : ℂ)).natDegree := IntermediateField.adjoin.finrank (isIntegral_sqrt_nat 2)
      _ ≤ 2 := minpoly_sqrt_deg 2
  -- Step 7.8: Bound [K₁(√5) : K₁] ≤ 2.
  -- √5 satisfies X² - 5 over K₁ (which is monic of degree 2), so the minimal polynomial
  -- of √5 over K₁ divides X² - 5 and has degree ≤ 2.
  have K1_K2_finrank_le : Module.finrank K1 K1_sqrt5 ≤ 2 := by
    rw [IntermediateField.adjoin.finrank h_int_5_K1]
    have hp : Polynomial.aeval (R := K1) (Real.sqrt 5 : ℂ) (X ^ 2 - C (5 : K1)) = 0 := by
      simp only [Polynomial.aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
                 IntermediateField.algebraMap_apply]
      rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      simp only [sub_eq_zero]; norm_cast
    have hmonic : (X ^ 2 - C (5 : K1)).Monic := monic_X_pow_sub_C _ (by norm_num)
    have hdeg_le := minpoly.min K1 (Real.sqrt 5 : ℂ) hmonic hp
    have hdeg_p : (X ^ 2 - C (5 : K1)).degree = 2 := degree_X_pow_sub_C (by norm_num) _
    rw [hdeg_p] at hdeg_le; exact Polynomial.natDegree_le_of_degree_le hdeg_le
  -- Step 7.9: Bound [K₂(√7) : K₂] ≤ 2. (Same argument as Step 7.8 with √7 and X² - 7.)
  have K2_K3_finrank_le : Module.finrank K2 K2_sqrt7 ≤ 2 := by
    rw [IntermediateField.adjoin.finrank h_int_7_K2]
    have hp : Polynomial.aeval (R := K2) (Real.sqrt 7 : ℂ) (X ^ 2 - C (7 : K2)) = 0 := by
      simp only [Polynomial.aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
                 IntermediateField.algebraMap_apply]
      rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 7)]
      simp only [sub_eq_zero]; norm_cast
    have hmonic : (X ^ 2 - C (7 : K2)).Monic := monic_X_pow_sub_C _ (by norm_num)
    have hdeg_le := minpoly.min K2 (Real.sqrt 7 : ℂ) hmonic hp
    have hdeg_p : (X ^ 2 - C (7 : K2)).degree = 2 := degree_X_pow_sub_C (by norm_num) _
    rw [hdeg_p] at hdeg_le; exact Polynomial.natDegree_le_of_degree_le hdeg_le
  -- Step 7.10: Bound [K₃(√11) : K₃] ≤ 2. (Same argument with √11 and X² - 11.)
  have K3_K_finrank_le : Module.finrank K3 K3_sqrt11 ≤ 2 := by
    rw [IntermediateField.adjoin.finrank h_int_11_K3]
    have hp : Polynomial.aeval (R := K3) (Real.sqrt 11 : ℂ) (X ^ 2 - C (11 : K3)) = 0 := by
      simp only [Polynomial.aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
                 IntermediateField.algebraMap_apply]
      rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 11)]
      simp only [sub_eq_zero]; norm_cast
    have hmonic : (X ^ 2 - C (11 : K3)).Monic := monic_X_pow_sub_C _ (by norm_num)
    have hdeg_le := minpoly.min K3 (Real.sqrt 11 : ℂ) hmonic hp
    have hdeg_p : (X ^ 2 - C (11 : K3)).degree = 2 := degree_X_pow_sub_C (by norm_num) _
    rw [hdeg_p] at hdeg_le; exact Polynomial.natDegree_le_of_degree_le hdeg_le
  -- Step 8: Combine the tower bounds to get [K : ℚ] ≤ 16.
  -- Step 8.1: [K₂ : ℚ] = [K₁(√5) : ℚ] = [K₁:ℚ] · [K₁(√5):K₁] ≤ 2 · 2 = 4.
  have K2_finrank_le : Module.finrank ℚ K2 ≤ 4 := by
    rw [K2_eq]
    calc Module.finrank ℚ (IntermediateField.restrictScalars ℚ K1_sqrt5)
        = Module.finrank ℚ K1_sqrt5 := rfl
      _ = Module.finrank ℚ K1 * Module.finrank K1 K1_sqrt5 := (Module.finrank_mul_finrank ℚ K1 K1_sqrt5).symm
      _ ≤ 2 * 2 := Nat.mul_le_mul K1_finrank_le K1_K2_finrank_le
      _ = 4 := by norm_num
  -- Step 8.2: [K₃ : ℚ] = [K₂(√7) : ℚ] = [K₂:ℚ] · [K₂(√7):K₂] ≤ 4 · 2 = 8.
  have K3_finrank_le : Module.finrank ℚ K3 ≤ 8 := by
    rw [K3_eq]
    calc Module.finrank ℚ (IntermediateField.restrictScalars ℚ K2_sqrt7)
        = Module.finrank ℚ K2_sqrt7 := rfl
      _ = Module.finrank ℚ K2 * Module.finrank K2 K2_sqrt7 := (Module.finrank_mul_finrank ℚ K2 K2_sqrt7).symm
      _ ≤ 4 * 2 := Nat.mul_le_mul K2_finrank_le K2_K3_finrank_le
      _ = 8 := by norm_num
  -- Step 8.3: [K : ℚ] = [K₃(√11) : ℚ] = [K₃:ℚ] · [K₃(√11):K₃] ≤ 8 · 2 = 16.
  have hK_finrank : Module.finrank ℚ K ≤ 16 := by
    rw [K_eq]
    calc Module.finrank ℚ (IntermediateField.restrictScalars ℚ K3_sqrt11)
        = Module.finrank ℚ K3_sqrt11 := rfl
      _ = Module.finrank ℚ K3 * Module.finrank K3 K3_sqrt11 := (Module.finrank_mul_finrank ℚ K3 K3_sqrt11).symm
      _ ≤ 8 * 2 := Nat.mul_le_mul K3_finrank_le K3_K_finrank_le
      _ = 16 := by norm_num
  -- Step 9: Build K(a) and show [K(a) : K] ≤ 5.
  -- Step 9.1: Define Ka = K(a), the simple adjunction of a over K in ℂ.
  let Ka : IntermediateField K ℂ := IntermediateField.adjoin K {a}
  -- Step 9.2: Ka is finite-dimensional over K (since a is integral over K).
  haveI hKa_fin : FiniteDimensional K Ka := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; exact a_integral_over_K ha_root
  -- Step 9.3: [K(a) : K] = natDegree(minpoly K a) ≤ 5 (from Step 4.2).
  have hKa_rank : Module.finrank K Ka ≤ 5 := by
    rw [IntermediateField.adjoin.finrank (a_integral_over_K ha_root)]
    exact hdeg_K
  -- Step 10: Use the inclusion ℚ(a) ⊆ K(a) and tower law.
  -- Step 10.1: Establish the scalar tower ℚ → K → K(a) and finite-dimensionality over ℚ.
  haveI : IsScalarTower ℚ K Ka := IntermediateField.isScalarTower Ka
  haveI : FiniteDimensional ℚ Ka := Module.Finite.trans K Ka
  -- Step 10.2: View K(a) as a ℚ-intermediate field via restrictScalars.
  let Ka_Q := IntermediateField.restrictScalars ℚ Ka
  -- Step 10.3: Show ℚ(a) ⊆ K(a) (when both viewed as intermediate fields over ℚ).
  -- This holds because K(a) contains a (trivially) and contains ℚ (since K ⊇ ℚ).
  have hQa_le : Qa ≤ Ka_Q := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.mem_adjoin_simple_self K a
  -- Step 10.4: Register finite-dimensionality instances needed for the final calculation.
  haveI : FiniteDimensional ℚ Ka_Q := inferInstanceAs (FiniteDimensional ℚ Ka)
  haveI : FiniteDimensional ℚ Qa := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; exact ha_int
  -- Step 10.5: The inclusion ℚ(a) ↪ K(a) is an injective ℚ-linear map.
  -- This gives [ℚ(a) : ℚ] ≤ [K(a) : ℚ] (dimension of subspace ≤ dimension of space).
  have hinj : Function.Injective (IntermediateField.inclusion hQa_le).toLinearMap := by
    intro x y hxy
    have h1 : ((IntermediateField.inclusion hQa_le x : Ka_Q) : ℂ) =
              ((IntermediateField.inclusion hQa_le y : Ka_Q) : ℂ) := congrArg Subtype.val hxy
    exact Subtype.ext h1
  -- Step 10.6: Final calculation combining all the bounds:
  --   natDegree(minpoly ℚ a) = [ℚ(a) : ℚ]         (Step 2.6)
  --                          ≤ [K(a) : ℚ]          (Step 10.5, subspace dimension bound)
  --                          = [K : ℚ] · [K(a) : K] (tower law)
  --                          ≤ 16 · 5              (Steps 8.3 and 9.3)
  --                          = 80.                  (arithmetic)
  calc (minpoly ℚ a).natDegree
      = Module.finrank ℚ Qa := hfinrank.symm
    _ ≤ Module.finrank ℚ Ka_Q := LinearMap.finrank_le_finrank_of_injective hinj
    _ = Module.finrank ℚ Ka := rfl
    _ = Module.finrank ℚ K * Module.finrank K Ka := (Module.finrank_mul_finrank ℚ K Ka).symm
    _ ≤ 16 * 5 := Nat.mul_le_mul hK_finrank hKa_rank
    _ = 80 := by norm_num
