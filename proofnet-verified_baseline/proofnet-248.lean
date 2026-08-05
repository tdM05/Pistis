import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

set_option maxHeartbeats 400000



/-Informal Statement

Let $R=\mathbb{Z}[\sqrt{-n}]$ where $n$ is a squarefree integer greater than 3. Prove that $2, \sqrt{-n}$ and $1+\sqrt{-n}$ are irreducibles in $R$.
-/

/-Informal Proof

Suppose $a=a_1+a_2 \sqrt{-n}, b=b_1+b_2 \sqrt{-n} \in R$ are such that $2=a b$, then $N(a) N(b)=4$. Without loss of generality we can assume $N(a) \leq N(b)$, so $N(a)=1$ or $N(a)=2$. Suppose $N(a)=2$, then $a_1^2+n a_2^2=2$ and since $n>3$ we have $a_2=0$, which implies $a_1^2=2$, a contradiction. So $N(a)=1$ and $a$ is a unit. Therefore 2 is irreducible in $R$.

Suppose now $\sqrt{-n}=a b$, then $N(a) N(b)=n$ and we can assume $N(a)<$ $N(b)$ since $n$ is square free. Suppose $N(a)>1$, then $a_1^2+n a_2^2>1$ and $a_1^2+n a_2^2 \mid n$, so $a_2=0$, and therefore $a_1^2 \mid n$. Since $n$ is squarefree, $a_1=\pm 1$, a contradiction. Therefore $N(a)=1$ and so $a$ is a unit and $\sqrt{-n}$ is irreducible.

Suppose $1+\sqrt{-n}=a b$, then $N(a) N(b)=n+1$ and we can assume $N(a) \leq N(b)$. Suppose $N(a)>1$, then $a_1^2+n a_2^2>1$ and $a_1^2+n a_2^2 \mid n+1$. If $\left|a_2\right| \geq 2$, then since $n>3$ we have a contradiction since $N(a)$ is too large. If $\left|a_2\right|=1$, then $a_1^2+n$ divides $1+n$ and so $a_1=\pm 1$, and in either case $N(a)=n+1$ which contradicts $N(a) \leq N(b)$. If $a_2=0$ then $a_1^2\left(b_1^2+n b_2^2\right)=\left(a_1 b_1\right)^2+n\left(a_1 b_2\right)^2=n+1$. If $\left|a_1 b_2\right| \geq 2$ we have a contradiction. If $\left|a_1 b_2\right|=1$ then $a_1=\pm 1$ which contradicts $N(a)>1$. If $\left|a_1 b_2\right|=0$, then $b_2=0$ and so $a_1 b_1=\sqrt{-n}$, a contradiction. Therefore $N(a)=1$ and so $a$ is a unit and $1+\sqrt{-n}$ is irreducible.
-/

theorem Dummit_Foote_exercise_8_3_5a {n : ℤ} (hn0 : n > 3) (hn1 : Squarefree n) :
  Irreducible (2 : Zsqrtd $ -n) ∧
  Irreducible (⟨0, 1⟩ : Zsqrtd $ -n) ∧
  Irreducible (1 + ⟨0, 1⟩ : Zsqrtd $ -n) := by
  -- ============================================================================
  -- OVERVIEW: We prove all three elements are irreducible in Z[√(-n)] where n > 3
  -- is squarefree. The key tool is the norm: N(a + b√(-n)) = a² + n·b²
  -- For d = -n < 0, norm is always non-negative, and units have norm 1.
  -- Strategy: For each element x, show x is not a unit and if x = a*b then
  -- either a or b has norm 1 (hence is a unit).
  -- ============================================================================

  -- Step 0: Establish basic facts about n
  have hn_pos : 0 < n := by omega
  have hn_neg : -n < 0 := by omega
  have hn_nonpos : -n ≤ 0 := by omega

  -- Step 0.1: Helper lemma for norm formula in Z[√(-n)]
  -- For z = ⟨a, b⟩ in Zsqrtd (-n), norm(z) = a² - (-n)·b² = a² + n·b²
  have norm_formula : ∀ z : Zsqrtd (-n), z.norm = z.re^2 + n * z.im^2 := by
    intro z
    simp only [Zsqrtd.norm_def]
    ring

  -- Step 0.2: Units in Z[√(-n)] are exactly those with norm = 1
  have unit_iff_norm_one : ∀ z : Zsqrtd (-n), IsUnit z ↔ z.norm = 1 := fun z =>
    Iff.symm (Zsqrtd.norm_eq_one_iff' hn_nonpos z)

  -- Step 0.3: Norm is non-negative
  have norm_nonneg : ∀ z : Zsqrtd (-n), 0 ≤ z.norm := Zsqrtd.norm_nonneg hn_nonpos

  -- Step 0.4: Norm equals zero iff element equals zero
  have norm_zero_iff : ∀ z : Zsqrtd (-n), z.norm = 0 ↔ z = 0 := by
    intro z
    constructor
    · intro h
      rw [norm_formula] at h
      have h1 : z.re^2 ≥ 0 := sq_nonneg z.re
      have h2 : n * z.im^2 ≥ 0 := by nlinarith [sq_nonneg z.im]
      have h3 : z.re^2 = 0 := by nlinarith
      have h4 : n * z.im^2 = 0 := by nlinarith
      have hre : z.re = 0 := by nlinarith [sq_nonneg z.re]
      have him : z.im = 0 := by
        have := sq_nonneg z.im
        nlinarith
      ext <;> assumption
    · intro h
      rw [h]
      simp [Zsqrtd.norm_def]

  -- ============================================================================
  -- PART 1: Prove 2 is irreducible in Z[√(-n)]
  -- ============================================================================
  refine ⟨?irred2, ?irredSqrt, ?irredOnePlusSqrt⟩

  case irred2 =>
    -- Step 1: Use the characterization of irreducibility
    rw [irreducible_iff]
    constructor
    -- Step 1.1: Show 2 is not a unit
    -- A unit has norm 1, but norm(2) = 4
    · intro h2unit
      rw [unit_iff_norm_one] at h2unit
      have hnorm2 : (2 : Zsqrtd (-n)).norm = 4 := by
        simp only [Zsqrtd.norm_def]
        norm_num
      linarith

    -- Step 1.2: Show if 2 = a * b then a or b is a unit
    · intro a b hab
      -- Step 1.2.1: Take norms: N(2) = N(a) * N(b)
      have hnorm_eq : (2 : Zsqrtd (-n)).norm = a.norm * b.norm := by
        calc (2 : Zsqrtd (-n)).norm = (a * b).norm := by rw [hab]
          _ = a.norm * b.norm := Zsqrtd.norm_mul a b
      have hnorm2 : (2 : Zsqrtd (-n)).norm = 4 := by
        simp only [Zsqrtd.norm_def]; norm_num
      rw [hnorm2] at hnorm_eq
      -- Step 1.2.2: Both norms are non-negative
      have ha_nn := norm_nonneg a
      have hb_nn := norm_nonneg b
      -- Step 1.2.3: Neither factor can be zero (since 2 ≠ 0)
      have ha_pos : 0 < a.norm := by
        by_contra h; push_neg at h
        have hzero := le_antisymm h ha_nn
        rw [norm_zero_iff] at hzero
        rw [hzero, zero_mul] at hab
        simp at hab
      have hb_pos : 0 < b.norm := by
        by_contra h; push_neg at h
        have hzero := le_antisymm h hb_nn
        rw [norm_zero_iff] at hzero
        rw [hzero, mul_zero] at hab
        simp at hab
      -- Step 1.2.4: a.norm divides 4, and a.norm > 0, so a.norm ∈ {1, 2, 4}
      have hdiv : a.norm ∣ 4 := ⟨b.norm, hnorm_eq⟩
      have ha_bound : a.norm ≤ 4 := Int.le_of_dvd (by linarith) hdiv
      -- Step 1.2.5: Case analysis on a.norm
      -- a.norm divides 4 and 1 ≤ a.norm ≤ 4, so a.norm ∈ {1, 2, 4}
      have hcases : a.norm = 1 ∨ a.norm = 2 ∨ a.norm = 4 := by
        have h1 : a.norm ≥ 1 := by linarith
        have h4 : a.norm * b.norm = 4 := hnorm_eq.symm
        -- Check: if a.norm = 3, then 3 | 4 which is false
        have hnot3 : a.norm ≠ 3 := by
          intro heq
          -- If a.norm = 3 and a.norm * b.norm = 4, then 3 * b.norm = 4
          -- But b.norm is a positive integer, and 3 * 1 = 3 < 4, 3 * 2 = 6 > 4
          -- So there's no integer b.norm satisfying this
          rw [heq] at h4
          have hb_ge1 : b.norm ≥ 1 := by linarith
          have hb_le1 : b.norm ≤ 1 := by nlinarith
          have hb_eq1 : b.norm = 1 := by linarith
          rw [hb_eq1] at h4
          norm_num at h4
        -- Now a.norm ∈ {1, 2, 4} since 1 ≤ a.norm ≤ 4 and a.norm ≠ 3
        omega

      rcases hcases with ha1 | ha2 | ha4
      · -- Case a.norm = 1: a is a unit
        left
        rw [unit_iff_norm_one]
        exact ha1
      · -- Case a.norm = 2: contradiction
        exfalso
        rw [norm_formula] at ha2
        -- If a.im ≠ 0, then |a.im| ≥ 1, so a.im² ≥ 1, so n·a.im² ≥ n > 3
        -- Then a.re² + n·a.im² > 3 > 2, contradiction
        -- So a.im = 0, then a.re² = 2, which is impossible for integers
        have him_sq : a.im^2 ≥ 0 := sq_nonneg a.im
        have hre_sq : a.re^2 ≥ 0 := sq_nonneg a.re
        by_cases him0 : a.im = 0
        · -- a.im = 0, so a.re² = 2
          rw [him0] at ha2
          simp at ha2
          -- a.re² = 2 has no integer solutions
          have hre_sq_2 : a.re^2 = 2 := ha2
          have hre_abs : a.re = 0 ∨ a.re = 1 ∨ a.re = -1 ∨ (a.re ≥ 2 ∨ a.re ≤ -2) := by omega
          rcases hre_abs with h | h | h | h
          · rw [h] at hre_sq_2; simp at hre_sq_2
          · rw [h] at hre_sq_2; simp at hre_sq_2
          · rw [h] at hre_sq_2; simp at hre_sq_2
          · rcases h with hge | hle
            · have : a.re^2 ≥ 4 := by nlinarith
              linarith
            · have : a.re^2 ≥ 4 := by nlinarith
              linarith
        · -- a.im ≠ 0, so |a.im| ≥ 1, hence a.im² ≥ 1
          have him_nz : a.im ≠ 0 := him0
          have him_sq_pos : a.im^2 ≥ 1 := by
            have : a.im = 0 ∨ a.im ≥ 1 ∨ a.im ≤ -1 := by omega
            rcases this with h | h | h
            · exact absurd h him_nz
            · nlinarith
            · nlinarith
          -- n·a.im² ≥ n > 3 > 2
          have : n * a.im^2 ≥ n := by nlinarith
          nlinarith
      · -- Case a.norm = 4: then b.norm = 1, so b is a unit
        right
        have hb1 : b.norm = 1 := by nlinarith
        rw [unit_iff_norm_one]
        exact hb1

  -- ============================================================================
  -- PART 2: Prove √(-n) = ⟨0, 1⟩ is irreducible in Z[√(-n)]
  -- ============================================================================
  case irredSqrt =>
    rw [irreducible_iff]
    constructor
    -- Step 2.1: Show ⟨0, 1⟩ is not a unit
    -- norm(⟨0, 1⟩) = 0² + n·1² = n ≠ 1 (since n > 3)
    · intro hunit
      rw [unit_iff_norm_one] at hunit
      have hnorm : (⟨0, 1⟩ : Zsqrtd (-n)).norm = n := by
        rw [norm_formula]; ring
      linarith

    -- Step 2.2: Show if ⟨0, 1⟩ = a * b then a or b is a unit
    · intro a b hab
      -- Step 2.2.1: Take norms: N(⟨0,1⟩) = N(a) * N(b) = n
      have hnorm_eq : (⟨0, 1⟩ : Zsqrtd (-n)).norm = a.norm * b.norm := by
        calc (⟨0, 1⟩ : Zsqrtd (-n)).norm = (a * b).norm := by rw [hab]
          _ = a.norm * b.norm := Zsqrtd.norm_mul a b
      have hnorm_sqrtd : (⟨0, 1⟩ : Zsqrtd (-n)).norm = n := by
        rw [norm_formula]; ring
      rw [hnorm_sqrtd] at hnorm_eq
      -- Step 2.2.2: Both norms are non-negative
      have ha_nn := norm_nonneg a
      have hb_nn := norm_nonneg b
      -- Step 2.2.3: Neither can be zero
      have ha_pos : 0 < a.norm := by
        by_contra h; push_neg at h
        have hzero := le_antisymm h ha_nn
        rw [norm_zero_iff] at hzero
        rw [hzero, zero_mul] at hab
        have : (⟨0, 1⟩ : Zsqrtd (-n)) ≠ 0 := by
          intro heq
          simp only [Zsqrtd.ext_iff] at heq
          obtain ⟨_, him⟩ := heq
          simp at him
        exact this hab
      have hb_pos : 0 < b.norm := by
        by_contra h; push_neg at h
        have hzero := le_antisymm h hb_nn
        rw [norm_zero_iff] at hzero
        rw [hzero, mul_zero] at hab
        have : (⟨0, 1⟩ : Zsqrtd (-n)) ≠ 0 := by
          intro heq
          simp only [Zsqrtd.ext_iff] at heq
          obtain ⟨_, him⟩ := heq
          simp at him
        exact this hab
      -- Step 2.2.4: a.norm * b.norm = n with n squarefree
      have hdiv : a.norm ∣ n := ⟨b.norm, hnorm_eq⟩
      have ha_bound : a.norm ≤ n := Int.le_of_dvd hn_pos hdiv
      -- Step 2.2.5: Case analysis
      by_cases h1 : a.norm = 1
      · left; rw [unit_iff_norm_one]; exact h1
      · by_cases hn' : a.norm = n
        · right; rw [unit_iff_norm_one]
          have : b.norm = 1 := by nlinarith
          exact this
        · -- Case: 1 < a.norm < n
          exfalso
          have ha_gt1 : a.norm > 1 := by
            have h1' : a.norm ≥ 1 := by linarith
            omega
          have ha_ltn : a.norm < n := by
            have hle := Int.le_of_dvd hn_pos hdiv
            omega
          -- a.norm = a.re² + n·a.im²
          -- If a.im ≠ 0, then a.norm ≥ n·a.im² ≥ n·1 = n, contradiction
          have him0 : a.im = 0 := by
            by_contra hne
            have him_sq_pos : a.im^2 ≥ 1 := by
              have : a.im = 0 ∨ a.im ≥ 1 ∨ a.im ≤ -1 := by omega
              rcases this with h | h | h
              · exact absurd h hne
              · nlinarith
              · nlinarith
            have : a.norm ≥ n * 1 := by
              rw [norm_formula]
              have := sq_nonneg a.re
              nlinarith
            linarith
          -- So a.im = 0, meaning a.norm = a.re²
          have ha_norm_eq : a.norm = a.re^2 := by
            rw [norm_formula, him0]; ring
          -- a.re² | n with 1 < a.re² < n and n squarefree
          -- Since n is squarefree, no perfect square > 1 can divide n
          have hsq : a.re^2 ∣ n := by
            rw [← ha_norm_eq]; exact hdiv
          -- Use squarefree property: if m² | n then m is a unit
          have hre_sq_form : (a.re.natAbs : ℤ) * (a.re.natAbs : ℤ) ∣ n := by
            have : a.re^2 = (a.re.natAbs : ℤ) * (a.re.natAbs : ℤ) := by ring_nf; simp [sq_abs]
            rw [← this]; exact hsq
          have hunit_int := hn1 a.re.natAbs hre_sq_form
          -- A unit in ℤ is ±1. Since a.re.natAbs is a Nat cast, it's a unit iff = 1
          have habs_1 : a.re.natAbs = 1 := by
            rw [Int.isUnit_iff] at hunit_int
            rcases hunit_int with h | h
            · exact Int.ofNat_injective h
            · have : (a.re.natAbs : ℤ) ≥ 0 := by simp
              omega
          -- So a.re = ±1, hence a.re² = 1
          have hre_sq_1 : a.re^2 = 1 := by
            have : a.re = 1 ∨ a.re = -1 := by
              cases Int.natAbs_eq a.re with
              | inl h => left; rw [h, habs_1]; rfl
              | inr h => right; rw [h, habs_1]; ring
            rcases this with h | h <;> simp [h]
          rw [ha_norm_eq, hre_sq_1] at ha_gt1
          linarith

  -- ============================================================================
  -- PART 3: Prove 1 + √(-n) = 1 + ⟨0, 1⟩ = ⟨1, 1⟩ is irreducible in Z[√(-n)]
  -- ============================================================================
  case irredOnePlusSqrt =>
    -- Note: 1 + ⟨0, 1⟩ = ⟨1, 0⟩ + ⟨0, 1⟩ = ⟨1, 1⟩
    have hone_plus : (1 : Zsqrtd (-n)) + ⟨0, 1⟩ = ⟨1, 1⟩ := by
      ext <;> simp
    rw [hone_plus]
    rw [irreducible_iff]
    constructor
    -- Step 3.1: Show ⟨1, 1⟩ is not a unit
    -- norm(⟨1, 1⟩) = 1² + n·1² = 1 + n ≠ 1 (since n > 3)
    · intro hunit
      rw [unit_iff_norm_one] at hunit
      have hnorm : (⟨1, 1⟩ : Zsqrtd (-n)).norm = 1 + n := by
        rw [norm_formula]; ring
      linarith

    -- Step 3.2: Show if ⟨1, 1⟩ = a * b then a or b is a unit
    · intro a b hab
      -- Step 3.2.1: Take norms: N(⟨1,1⟩) = N(a) * N(b) = 1 + n
      have hnorm_eq : (⟨1, 1⟩ : Zsqrtd (-n)).norm = a.norm * b.norm := by
        calc (⟨1, 1⟩ : Zsqrtd (-n)).norm = (a * b).norm := by rw [hab]
          _ = a.norm * b.norm := Zsqrtd.norm_mul a b
      have hnorm_elem : (⟨1, 1⟩ : Zsqrtd (-n)).norm = 1 + n := by
        rw [norm_formula]; ring
      rw [hnorm_elem] at hnorm_eq
      -- Step 3.2.2: Non-negativity
      have ha_nn := norm_nonneg a
      have hb_nn := norm_nonneg b
      -- Step 3.2.3: Neither zero
      have ha_pos : 0 < a.norm := by
        by_contra h; push_neg at h
        have hzero := le_antisymm h ha_nn
        rw [norm_zero_iff] at hzero
        rw [hzero, zero_mul] at hab
        have : (⟨1, 1⟩ : Zsqrtd (-n)) ≠ 0 := by
          intro heq
          simp only [Zsqrtd.ext_iff] at heq
          obtain ⟨hre, _⟩ := heq
          simp at hre
        exact this hab
      have hb_pos : 0 < b.norm := by
        by_contra h; push_neg at h
        have hzero := le_antisymm h hb_nn
        rw [norm_zero_iff] at hzero
        rw [hzero, mul_zero] at hab
        have : (⟨1, 1⟩ : Zsqrtd (-n)) ≠ 0 := by
          intro heq
          simp only [Zsqrtd.ext_iff] at heq
          obtain ⟨hre, _⟩ := heq
          simp at hre
        exact this hab
      -- Step 3.2.4: Divisibility
      have hdiv : a.norm ∣ (1 + n) := ⟨b.norm, hnorm_eq⟩
      have ha_bound : a.norm ≤ 1 + n := Int.le_of_dvd (by linarith) hdiv
      -- Step 3.2.5: Case analysis
      by_cases h1 : a.norm = 1
      · left; rw [unit_iff_norm_one]; exact h1
      · by_cases hn' : a.norm = 1 + n
        · right; rw [unit_iff_norm_one]
          have : b.norm = 1 := by nlinarith
          exact this
        · -- Case: 1 < a.norm < 1 + n
          exfalso
          have ha_gt1 : a.norm > 1 := by
            have h1' : a.norm ≥ 1 := by linarith
            omega
          have ha_lt1n : a.norm < 1 + n := by
            have hle := Int.le_of_dvd (by linarith : 0 < 1 + n) hdiv
            omega
          -- Step 3.2.5.1: Analyze possible values of a.im
          -- If |a.im| ≥ 2, then a.norm ≥ n·4 ≥ 4n > 1+n for n > 3, contradiction
          have him_small : a.im^2 ≤ 1 := by
            by_contra h; push_neg at h
            have him_sq_ge2 : a.im^2 ≥ 2 := by
              have := sq_nonneg a.im
              linarith
            have : a.norm ≥ n * 2 := by
              rw [norm_formula]
              have := sq_nonneg a.re
              nlinarith
            -- n * 2 > 1 + n since n > 3 means n > 1
            linarith
          -- So |a.im| ≤ 1, i.e., a.im ∈ {-1, 0, 1}
          have him_cases : a.im = -1 ∨ a.im = 0 ∨ a.im = 1 := by
            have h1 : a.im^2 ≤ 1 := him_small
            have h2 : a.im^2 ≥ 0 := sq_nonneg a.im
            have habs : a.im ≥ -1 ∧ a.im ≤ 1 := by
              constructor
              · by_contra hc; push_neg at hc
                have : a.im^2 ≥ 4 := by nlinarith
                linarith
              · by_contra hc; push_neg at hc
                have : a.im^2 ≥ 4 := by nlinarith
                linarith
            omega

          rcases him_cases with him_m1 | him_0 | him_1
          -- Case: a.im = -1, so a.norm = a.re² + n
          · have ha_norm_eq : a.norm = a.re^2 + n := by
              rw [norm_formula, him_m1]; ring
            -- a.re² + n | 1 + n and 1 < a.re² + n < 1 + n
            -- If a.re² = 0, then a.norm = n, and n | 1+n, so n | 1, contradiction
            -- If a.re² = 1, then a.norm = 1+n, contradiction with ha_lt1n
            have hre_sq : a.re^2 ≥ 0 := sq_nonneg a.re
            have hre_sq_bound : a.re^2 < 1 := by linarith
            have hre_zero : a.re = 0 := by
              -- a.re^2 < 1 and a.re^2 ≥ 0 means a.re^2 = 0
              have hre_sq_0 : a.re^2 = 0 := by linarith
              nlinarith [sq_nonneg a.re]
            -- Now a.norm = 0 + n = n
            have ha_norm_n : a.norm = n := by rw [ha_norm_eq, hre_zero]; ring
            -- n | 1+n means n | 1
            have hdiv' : n ∣ (1 + n) := by
              convert hdiv using 2
              exact ha_norm_n.symm
            have hdiv_1 : n ∣ (1 : ℤ) := by
              have : n ∣ (1 + n) - n := Int.dvd_sub hdiv' (dvd_refl n)
              simp at this
              exact this
            have := Int.eq_one_of_dvd_one (by linarith : 0 ≤ n) hdiv_1
            linarith

          -- Case: a.im = 0, so a.norm = a.re²
          · have ha_norm_eq : a.norm = a.re^2 := by
              rw [norm_formula, him_0]; ring
            have hre_nz : a.re ≠ 0 := by
              intro h
              rw [h] at ha_norm_eq
              simp at ha_norm_eq
              linarith
            have hre_abs_ge2 : a.re ≥ 2 ∨ a.re ≤ -2 := by
              have hre_sq_gt1 : a.re^2 > 1 := by linarith
              by_contra hc; push_neg at hc
              have : a.re ≥ -1 ∧ a.re ≤ 1 := by omega
              have : a.re = -1 ∨ a.re = 0 ∨ a.re = 1 := by omega
              rcases this with h | h | h
              · rw [h] at hre_sq_gt1; simp at hre_sq_gt1
              · exact hre_nz h
              · rw [h] at hre_sq_gt1; simp at hre_sq_gt1
            -- Now a = ⟨a.re, 0⟩, so a * b = ⟨a.re * b.re + d * 0 * b.im, a.re * b.im + 0 * b.re⟩
            --                           = ⟨a.re * b.re, a.re * b.im⟩
            -- Extract the product equation
            have hprod : a * b = ⟨1, 1⟩ := hab.symm
            -- Expand multiplication in Zsqrtd
            have ha_eq : a = ⟨a.re, 0⟩ := by ext <;> simp [him_0]
            rw [ha_eq] at hprod
            -- ⟨a.re, 0⟩ * b = ⟨a.re * b.re + (-n) * 0 * b.im, a.re * b.im + 0 * b.re⟩
            --                = ⟨a.re * b.re, a.re * b.im⟩
            simp only [Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul] at hprod
            obtain ⟨hprod_re, hprod_im⟩ := hprod
            simp only [mul_zero, zero_mul, add_zero] at hprod_re hprod_im
            -- So a.re * b.re = 1 and a.re * b.im = 1
            -- a.re * b.re = 1 means a.re | 1, so |a.re| = 1, so a.re² = 1
            have hdiv1 : a.re ∣ 1 := ⟨b.re, hprod_re.symm⟩
            have habs_1 : a.re = 1 ∨ a.re = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one hdiv1)
            rcases habs_1 with h | h <;> (rcases hre_abs_ge2 with hge | hle <;> linarith)

          -- Case: a.im = 1, so a.norm = a.re² + n (same as a.im = -1 case)
          · have ha_norm_eq : a.norm = a.re^2 + n := by
              rw [norm_formula, him_1]; ring
            have hre_sq : a.re^2 ≥ 0 := sq_nonneg a.re
            have hre_sq_bound : a.re^2 < 1 := by linarith
            have hre_zero : a.re = 0 := by
              -- a.re^2 < 1 and a.re^2 ≥ 0 means a.re^2 = 0
              have hre_sq_0 : a.re^2 = 0 := by linarith
              nlinarith [sq_nonneg a.re]
            -- Now a.norm = 0 + n = n
            have ha_norm_n : a.norm = n := by rw [ha_norm_eq, hre_zero]; ring
            have hdiv' : n ∣ (1 + n) := by
              convert hdiv using 2
              exact ha_norm_n.symm
            have hdiv_1 : n ∣ (1 : ℤ) := by
              have : n ∣ (1 + n) - n := Int.dvd_sub hdiv' (dvd_refl n)
              simp at this
              exact this
            have := Int.eq_one_of_dvd_one (by linarith : 0 ≤ n) hdiv_1
            linarith
