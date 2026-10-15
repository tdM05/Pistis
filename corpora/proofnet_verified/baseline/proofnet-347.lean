import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Suppose $f$ is a real function defined on $\mathbb{R}$ which satisfies $\lim_{h \rightarrow 0} f(x + h) - f(x - h) = 0$ for every $x \in \mathbb{R}$. Show that $f$ does not need to be continuous.
-/

/-Informal Proof

$$
f(x)= \begin{cases}1 & \text { if } x \text { is an integer } \\ 0 & \text { if } x \text { is not an integer. }\end{cases}
$$
(If $x$ is an integer, then $f(x+h)-f(x-h) \equiv 0$ for all $h$; while if $x$ is not an integer, $f(x+h)-f(x-h)=0$ for $|h|<\min (x-[x], 1+[x]-x)$.
-/

theorem Rudin_exercise_4_1a
  : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Tendsto (λ y => f (x + y) - f (x - y)) (𝓝 0) (𝓝 0)) ∧ ¬ Continuous f := by
  -- Step 1: Enable classical reasoning so that every `if`-expression can decide membership in ℤ.
  classical
  -- Step 2: Define the integer predicate and the associated indicator function.
  let isInteger : ℝ → Prop := fun x => ∃ z : ℤ, x = z
  let f : ℝ → ℝ := fun x => if isInteger x then 1 else 0
  -- Step 2.1: Record the elementary closure properties of the predicate.
  have h_add :
      ∀ {u v : ℝ}, isInteger u → isInteger v → isInteger (u + v) := by
    intro u v hu hv
    rcases hu with ⟨m, rfl⟩
    rcases hv with ⟨n, rfl⟩
    refine ⟨m + n, ?_⟩
    simp
  have h_sub :
      ∀ {u v : ℝ}, isInteger u → isInteger v → isInteger (u - v) := by
    intro u v hu hv
    rcases hu with ⟨m, rfl⟩
    rcases hv with ⟨n, rfl⟩
    refine ⟨m - n, ?_⟩
    simp
  have h_neg :
      ∀ {u : ℝ}, isInteger u → isInteger (-u) := by
    intro u hu
    rcases hu with ⟨m, rfl⟩
    refine ⟨-m, ?_⟩
    simp
  have h_of_add :
      ∀ {u v : ℝ}, isInteger (u + v) → isInteger u → isInteger v := by
    intro u v hsum hu
    have := h_sub hsum hu
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have h_of_sub :
      ∀ {u v : ℝ}, isInteger (u - v) → isInteger u → isInteger v := by
    intro u v hdiff hu
    have := h_sub hu hdiff
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Step 3: Prove that for every center x there is a symmetric radius where the difference is identically 0.
  have hlimit_aux :
      ∀ x : ℝ, ∃ ε > 0, ∀ ⦃y : ℝ⦄, |y| < ε → f (x + y) - f (x - y) = 0 := by
    intro x
    -- Step 3.1: Split according to whether x itself is an integer.
    by_cases hx : isInteger x
    · -- Step 3.1.1: For integral x choose ε = 1/2 so that only y = 0 could still be integral.
      refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
      intro y hy
      -- Step 3.1.2: Characterize the integer status of x ± y using the fact that x is already integral.
      have hx_int : isInteger x := hx
      have hxpy_iff : isInteger (x + y) ↔ isInteger y :=
        ⟨fun h => h_of_add h hx_int, fun hy => h_add hx_int hy⟩
      have hxmy_iff : isInteger (x - y) ↔ isInteger y :=
        ⟨fun h => h_of_sub h hx_int, fun hy => by
          have := h_add hx_int (h_neg hy)
          simpa [sub_eq_add_neg] using this⟩
      -- Step 3.1.3: Show that the only integral y with |y| < 1/2 is y = 0.
      have hy_zero_of_int : isInteger y → y = 0 := by
        intro hyInt
        rcases hyInt with ⟨k, hk⟩
        have hk_abs : |(k : ℝ)| < (1 : ℝ) / 2 := by simpa [hk] using hy
        have hk_abs_lt_one : |(k : ℝ)| < 1 := lt_trans hk_abs (by norm_num)
        have hk_bounds := abs_lt.mp hk_abs_lt_one
        have hk_nonneg : 0 ≤ k := by
          have hk_int : (-1 : ℤ) < k := by exact_mod_cast hk_bounds.1
          by_contra hneg
          have hk_lt_zero : k < 0 := lt_of_not_ge hneg
          have hk_lt' : k < (-1 : ℤ) + 1 := by simpa using hk_lt_zero
          have hk_le_neg_one : k ≤ -1 := (Int.lt_add_one_iff.mp hk_lt')
          exact (lt_irrefl _ (lt_of_le_of_lt hk_le_neg_one hk_int))
        have hk_nonpos : k ≤ 0 := by
          have hk_lt_one : k < 0 + 1 := by
            have : (k : ℝ) < 1 := hk_bounds.2
            have : k < (1 : ℤ) := by exact_mod_cast this
            simpa using this
          have := (Int.lt_add_one_iff.mp hk_lt_one)
          simpa using this
        have hk_zero : k = 0 := le_antisymm hk_nonpos hk_nonneg
        simp [hk, hk_zero]
      -- Step 3.1.4: Distinguish the integer and non-integer cases for y and conclude that the difference vanishes.
      by_cases hyInt : isInteger y
      · have hyzero : y = 0 := hy_zero_of_int hyInt
        simp [f, hx, hyzero]
      · have hxpy_not : ¬ isInteger (x + y) := by
          intro hxy
          exact hyInt (hxpy_iff.mp hxy)
        have hxmy_not : ¬ isInteger (x - y) := by
          intro hxy
          exact hyInt (hxmy_iff.mp hxy)
        simp [f, hxpy_not, hxmy_not]
    · -- Step 3.2: When x is not an integer, stay inside the open interval between consecutive integers.
      set n : ℤ := Int.floor x with hn_def
      have hx_not : ¬ isInteger x := hx
      have hle : (n : ℝ) ≤ x := by
        simpa [hn_def] using (Int.floor_le x)
      have hxne : (n : ℝ) ≠ x := by
        intro hx_eq
        apply hx_not
        exact ⟨n, hx_eq.symm⟩
      have hxgt : (n : ℝ) < x := lt_of_le_of_ne hle hxne
      have hxlt : x < (n + 1 : ℤ) := by
        simp [hn_def]
      let δ : ℝ :=
        min (x - (n : ℝ)) (((n + 1 : ℤ) : ℝ) - x)
      have hδpos :
          0 < δ :=
        (lt_min_iff).2
          ⟨sub_pos.mpr hxgt, sub_pos.mpr hxlt⟩
      -- Step 3.2.1: Use |y| < δ to put x ± y strictly between n and n + 1.
      refine ⟨δ, hδpos, ?_⟩
      intro y hy
      have hy_lt_left : |y| < x - (n : ℝ) :=
        lt_of_lt_of_le hy (min_le_left _ _)
      have hy_lt_right :
          |y| < ((n + 1 : ℤ) : ℝ) - x :=
        lt_of_lt_of_le hy (min_le_right _ _)
      have hy_left := abs_lt.mp hy_lt_left
      have hy_right := abs_lt.mp hy_lt_right
      -- Step 3.2.2: Record inequalities showing that both x + y and x - y remain inside the interval.
      have hxpy_gt : (n : ℝ) < x + y := by
        have := hy_left.1
        have := add_lt_add_left this x
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have hy_upper : y < (n : ℝ) + 1 - x := by
        simpa [Int.cast_add, Int.cast_one, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc] using hy_right.2
      have hxpy_lt : x + y < (n : ℝ) + 1 := by
        have := hy_upper
        linarith
      have hxmy_gt : (n : ℝ) < x - y := by
        have := hy_left.2
        have := sub_lt_sub_left this x
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have hy_neg : -y < (n : ℝ) + 1 - x := by
        have := neg_lt_neg hy_right.1
        simpa [Int.cast_add, Int.cast_one, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc] using this
      have hxmy_lt : x - y < (n : ℝ) + 1 := by
        have := hy_neg
        linarith
      -- Step 3.2.3: A real strictly between consecutive integers cannot itself be an integer.
      have notIsInt_between :
          ∀ {r : ℝ}, (n : ℝ) < r → r < (n : ℝ) + 1 → ¬ isInteger r := by
        intro r hleft hright hInt
        rcases hInt with ⟨m, hm⟩
        have hnm_lt : n < m := by
          have : (n : ℝ) < (m : ℝ) := by simpa [hm] using hleft
          exact_mod_cast this
        have hm_le : m ≤ n := by
          have : (m : ℝ) < (n : ℝ) + 1 := by simpa [hm] using hright
          have : m < n + 1 := by exact_mod_cast this
          have := (Int.lt_add_one_iff).1 this
          simpa using this
        have : (n : ℤ) < n := lt_of_lt_of_le hnm_lt hm_le
        exact lt_irrefl _ this
      -- Step 3.2.4: Apply the non-integer conclusion to x ± y and finish.
      have hxpy_not : ¬ isInteger (x + y) :=
        notIsInt_between hxpy_gt hxpy_lt
      have hxmy_not : ¬ isInteger (x - y) :=
        notIsInt_between hxmy_gt hxmy_lt
      simp [f, hxpy_not, hxmy_not]
  -- Step 4: Turn the radius information into the Tendsto claim for each x.
  have hlimit :
      ∀ x : ℝ, Tendsto (fun y => f (x + y) - f (x - y)) (𝓝 0) (𝓝 0) := by
    intro x
    -- Step 4.1: Extract the ε-ball around 0 on which the difference is identically zero.
    obtain ⟨ε, hεpos, hε⟩ := hlimit_aux x
    have hball :
        {y : ℝ | |y| < ε} ∈ 𝓝 (0 : ℝ) := by
      have := Metric.ball_mem_nhds (0 : ℝ) hεpos
      simpa [Metric.ball, Real.dist_eq] using this
    have hset :
        {y : ℝ | |y| < ε} ⊆ {y : ℝ | f (x + y) - f (x - y) = 0} := by
      intro y hy
      exact hε hy
    have hzero :
        ∀ᶠ y in 𝓝 (0 : ℝ), f (x + y) - f (x - y) = 0 :=
      by
        exact Filter.mem_of_superset hball hset
    -- Step 4.2: Conclude that the map agrees eventually with the constant zero function.
    exact (tendsto_congr' hzero).mpr (by simp)
  -- Step 5: Exhibit that the chosen function fails to be continuous (at 0).
  refine ⟨f, hlimit, ?_⟩
  -- Step 5.1: Record the exact value of f at 0 (which equals 1).
  have hf0 : f 0 = 1 := by
    have : isInteger (0 : ℝ) := ⟨0, by norm_cast⟩
    simp [f, this]
  -- Step 5.2: Assume continuity and reach a contradiction by zooming in on a small non-integer y.
  refine fun hf => ?_
  have hcont0 : ContinuousAt f 0 := hf.continuousAt
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.continuousAt_iff.1 hcont0) ((1 : ℝ) / 2) (by norm_num)
  -- Step 5.3: Choose y = min(δ, 1)/2, which is close to 0 but still non-integral.
  set y : ℝ := (min δ 1) / 2 with hy_def
  have hmin_pos : 0 < min δ 1 := (lt_min_iff).2 ⟨hδpos, by norm_num⟩
  have hy_pos : 0 < y := by
    simpa [hy_def] using (half_pos hmin_pos)
  have hy_nonneg : 0 ≤ y := le_of_lt hy_pos
  have hy_ltδ : y < δ := by
    by_cases hδ : δ ≤ 1
    · have hy_eq : y = δ / 2 := by simp [hy_def, hδ]
      have : δ / 2 < δ := half_lt_self hδpos
      simpa [hy_eq] using this
    · have hδ' : 1 < δ := lt_of_not_ge hδ
      have hy_eq : y = (1 : ℝ) / 2 := by
        have : 1 ≤ δ := le_of_lt hδ'
        simp [hy_def, this]
      have : (1 : ℝ) / 2 < δ := lt_trans (by norm_num) hδ'
      simpa [hy_eq] using this
  have hy_abs_lt : |y| < δ := by
    simpa [abs_of_nonneg hy_nonneg] using hy_ltδ
  have hy_le_half : y ≤ (1 : ℝ) / 2 := by
    have hmin : min δ 1 / (2 : ℝ) ≤ 1 / 2 :=
      div_le_div_of_nonneg_right (min_le_right _ _)
        (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
    simpa [hy_def] using hmin
  have hy_lt_one : y < 1 := lt_of_le_of_lt hy_le_half (by norm_num)
  have hy_not_int : ¬ isInteger y := by
    intro hyInt
    rcases hyInt with ⟨k, hk⟩
    have hk_pos : 0 < k := by
      have : 0 < (k : ℝ) := by simpa [hk] using hy_pos
      exact_mod_cast this
    have hk_lt_one : k < 1 := by
      have : (k : ℝ) < 1 := by simpa [hk] using hy_lt_one
      exact_mod_cast this
    have hk_le_zero : k ≤ 0 := by
      have hk_lt_one' : k < 0 + 1 := by simpa using hk_lt_one
      exact (Int.lt_add_one_iff.mp hk_lt_one')
    exact (not_lt_of_ge hk_le_zero) hk_pos
  have hfy : f y = 0 := by simp [f, hy_not_int]
  -- Step 5.4: Evaluate the continuity inequality at y and contradict |f y - f 0| < 1/2.
  have hy_in : dist y 0 < δ := by simpa [Real.dist_eq, abs_sub_comm] using hy_abs_lt
  have hlt : |f y - f 0| < (1 : ℝ) / 2 := by
    simpa [Real.dist_eq] using hδ hy_in
  have habs : |f y - f 0| = 1 := by simp [hfy, hf0]
  have hcontra : (1 : ℝ) < (1 : ℝ) / 2 := by simpa [habs] using hlt
  have : ¬ (1 : ℝ) < (1 : ℝ) / 2 := by norm_num
  exact this hcontra
