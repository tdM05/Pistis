import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

noncomputable def f : ℕ → ℝ
| 0 => Real.sqrt 2
| (n + 1) => Real.sqrt (2 + Real.sqrt (f n))

@[simp] lemma f_succ (n : ℕ) : f (n + 1) = Real.sqrt (2 + Real.sqrt (f n)) := by
  -- Step 1: Unfold the recursive definition of `f` to read off the successor formula directly.
  rfl

noncomputable def contractionConstant : ℝ := 1 / (4 * Real.sqrt 3)

lemma contractionConstant_nonneg : 0 ≤ contractionConstant := by
  -- Step 1: Observe that both numerator and denominator of `1 / (4 * √3)` are nonnegative.
  refine div_nonneg (by norm_num) ?_
  -- Step 1.1: The denominator `4 * √3` is positive because each factor is positive.
  have : 0 < (4 : ℝ) * Real.sqrt 3 := by positivity
  exact this.le

lemma contractionConstant_lt_one : contractionConstant < 1 := by
  -- Step 1: Reduce the claim to the inequality `1 < 4 * √3` using the strict-monotone nature of inversion.
  have hden_pos : 0 < (1 : ℝ) := by norm_num
  have hden_lt : (1 : ℝ) < 4 * Real.sqrt 3 := by
    -- Step 1.1: First note `1 < 4`.
    have h_one_lt_four : (1 : ℝ) < 4 := by norm_num
    -- Step 1.2: Since `√3 ≥ 1`, multiplying by `4` preserves the inequality and refines the bound.
    have h_sqrt_ge_one : (1 : ℝ) ≤ Real.sqrt 3 := by
      have : (1 : ℝ) ≤ (3 : ℝ) := by norm_num
      simp
    have : (4 : ℝ) ≤ 4 * Real.sqrt 3 := by
      have h_four_nonneg : (0 : ℝ) ≤ 4 := by norm_num
      simp
    exact h_one_lt_four.trans_le this
  -- Step 2: Apply the reciprocal inequality to conclude `1 / (4 * √3) < 1`.
  have hrec := one_div_lt_one_div_of_lt hden_pos hden_lt
  simpa [contractionConstant] using hrec

lemma abs_sqrt_sub_sqrt_eq_div_of_pos {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    |Real.sqrt a - Real.sqrt b| = |a - b| / (Real.sqrt a + Real.sqrt b) := by
  -- Step 1: Record that the denominator is strictly positive so division is legitimate.
  have hpos : 0 < Real.sqrt a + Real.sqrt b :=
    add_pos (Real.sqrt_pos.2 ha) (Real.sqrt_pos.2 hb)
  -- Step 2: Use the difference-of-squares identity to express the numerator after clearing denominators.
  have hmul :
      (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
    have ha_nonneg : 0 ≤ a := ha.le
    have hb_nonneg : 0 ≤ b := hb.le
    have :
        (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) =
          (Real.sqrt a) ^ 2 - (Real.sqrt b) ^ 2 := by
      -- Step 2.1: Apply the algebraic identity `(u - v)(u + v) = u^2 - v^2`.
      ring
    -- Step 2.2: Replace the squares of the square roots with the original numbers.
    simp [this, pow_two, Real.mul_self_sqrt ha_nonneg,
      Real.mul_self_sqrt hb_nonneg]
  -- Step 3: Divide both sides of the last equality by the positive denominator and take absolute values.
  have hquot :
      Real.sqrt a - Real.sqrt b =
        (a - b) / (Real.sqrt a + Real.sqrt b) :=
    (eq_div_iff_mul_eq (ne_of_gt hpos)).2 hmul
  -- Step 3.1: Taking absolute values converts the equality into the desired ratio.
  have := congrArg (fun t : ℝ => |t|) hquot
  simpa [abs_div, abs_of_pos hpos] using this

lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  -- Step 1: Compare square roots via the inequality `2 < 4`.
  have := (Real.sqrt_lt' (by norm_num : 0 < (2 : ℝ))).2 (by norm_num : (2 : ℝ) < 2 ^ 2)
  simpa using this

lemma sqrt_two_le_f : ∀ n, Real.sqrt 2 ≤ f n := by
  -- Step 1: Prove the claim by induction on `n`.
  refine Nat.rec ?base ?step
  · -- Step 1.1: Base case `n = 0` is immediate from the definition.
    simp [f]
  · -- Step 1.2: For the inductive step, use monotonicity of `Real.sqrt`.
    intro n hn
    have h_inner : (2 : ℝ) ≤ 2 + Real.sqrt (f n) := by
      -- Step 1.2.1: The inner square root is nonnegative, so adding it preserves the inequality.
      have : 0 ≤ Real.sqrt (f n) := Real.sqrt_nonneg _
      linarith
    have h_nonneg : 0 ≤ (2 : ℝ) := by norm_num
    have h_target : 0 ≤ 2 + Real.sqrt (f n) := by
      have : 0 ≤ Real.sqrt (f n) := Real.sqrt_nonneg _
      linarith
    -- Step 1.2.2: Apply `sqrt_le_sqrt_iff` to conclude the desired inequality.
    have := (Real.sqrt_le_sqrt_iff h_target).2 h_inner
    simpa [f_succ] using this

lemma f_lt_two : ∀ n, f n < 2 := by
  -- Step 1: Again proceed by induction on `n`.
  refine Nat.rec ?base ?step
  · -- Step 1.1: Base case `n = 0` uses the explicit value `f 0 = √2 < 2`.
    simpa [f] using sqrt_two_lt_two
  · -- Step 1.2: For the inductive step, bound `f (n+1)` using the recursion.
    intro n hn
    -- Step 1.2.1: Compare the inner square root with `√2` thanks to the monotonicity of `sqrt`.
    have h_inner :
        Real.sqrt (f n) ≤ Real.sqrt 2 := by
      have h_le_two : f n ≤ 2 := le_of_lt hn
      exact Real.sqrt_le_sqrt h_le_two
    -- Step 1.2.2: Substitute the previous inequality into the expression for `f (n+1)`.
    have h_compare :
        f (n + 1) ≤ Real.sqrt (2 + Real.sqrt 2) := by
      refine Real.sqrt_le_sqrt ?_
      have h_nonneg : 0 ≤ Real.sqrt (f n) := Real.sqrt_nonneg _
      have h_rhs_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      simpa [f_succ] using add_le_add_left h_inner 2
    -- Step 1.2.3: Show the upper bound is itself strictly smaller than 2.
    have : Real.sqrt (2 + Real.sqrt 2) < 2 := by
      have h_lt : 2 + Real.sqrt 2 < (2 : ℝ) ^ 2 := by
        have h' : Real.sqrt 2 < 2 := sqrt_two_lt_two
        have : 2 + Real.sqrt 2 < 2 + 2 := by linarith
        simpa [pow_two, two_mul] using this
      have := (Real.sqrt_lt' (by norm_num : 0 < (2 : ℝ))).2 h_lt
      simpa using this
    exact lt_of_le_of_lt h_compare this

lemma lipschitz_update
    (x y : ℝ) (hx : Real.sqrt 2 ≤ x) (hy : Real.sqrt 2 ≤ y) :
    |Real.sqrt (2 + Real.sqrt x) - Real.sqrt (2 + Real.sqrt y)|
      ≤ contractionConstant * |x - y| := by
  -- Step 1: Establish positivity facts about all quantities appearing under square roots.
  have hx_pos : 0 < x := (lt_of_lt_of_le (Real.sqrt_pos.2 (by norm_num)) hx)
  have hy_pos : 0 < y := (lt_of_lt_of_le (Real.sqrt_pos.2 (by norm_num)) hy)
  have hx_sqrt_ge_one : (1 : ℝ) ≤ Real.sqrt x := by
    have h_one_le_x : (1 : ℝ) ≤ x := by
      have : (1 : ℝ) ≤ Real.sqrt 2 := by
        have : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
        simp
      exact this.trans hx
    simpa [Real.sqrt_one] using Real.sqrt_le_sqrt h_one_le_x
  have hy_sqrt_ge_one : (1 : ℝ) ≤ Real.sqrt y := by
    have h_one_le_y : (1 : ℝ) ≤ y := by
      have : (1 : ℝ) ≤ Real.sqrt 2 := by
        have : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
        simp
      exact this.trans hy
    simpa [Real.sqrt_one] using Real.sqrt_le_sqrt h_one_le_y
  -- Step 2: Rewrite the absolute difference by peeling off square roots twice.
  have h_outer' :
      |Real.sqrt (2 + Real.sqrt x) - Real.sqrt (2 + Real.sqrt y)|
        = |Real.sqrt x - Real.sqrt y| /
            (Real.sqrt (2 + Real.sqrt x) + Real.sqrt (2 + Real.sqrt y)) := by
    have :=
      abs_sqrt_sub_sqrt_eq_div_of_pos
        (by positivity : 0 < 2 + Real.sqrt x)
        (by positivity : 0 < 2 + Real.sqrt y)
    simpa [add_comm, add_left_comm, sub_eq_add_neg, add_assoc] using this
  have h_inner' :
      |Real.sqrt x - Real.sqrt y| = |x - y| / (Real.sqrt x + Real.sqrt y) := by
    simpa using abs_sqrt_sub_sqrt_eq_div_of_pos hx_pos hy_pos
  set s₁ := Real.sqrt x + Real.sqrt y with hs₁
  set s₂ := Real.sqrt (2 + Real.sqrt x) + Real.sqrt (2 + Real.sqrt y) with hs₂
  have hs₁_pos : 0 < s₁ := by
    have hx_sqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx_pos
    have hy_sqrt_pos : 0 < Real.sqrt y := Real.sqrt_pos.2 hy_pos
    simpa [hs₁] using add_pos hx_sqrt_pos hy_sqrt_pos
  have hs₂_pos : 0 < s₂ := by
    have hx_inner_pos : 0 < Real.sqrt (2 + Real.sqrt x) := Real.sqrt_pos.2 (by positivity)
    have hy_inner_pos : 0 < Real.sqrt (2 + Real.sqrt y) := Real.sqrt_pos.2 (by positivity)
    simpa [hs₂] using add_pos hx_inner_pos hy_inner_pos
  have h_rewrite :
      |Real.sqrt (2 + Real.sqrt x) - Real.sqrt (2 + Real.sqrt y)|
        = |x - y| / (s₁ * s₂) := by
    simp [hs₁, hs₂, h_outer', h_inner', div_eq_mul_inv, mul_comm, mul_assoc]
  -- Step 3: Produce the universal lower bound on the denominator.
  have h_sum_ge_two : (2 : ℝ) ≤ s₁ := by
    have h := add_le_add hx_sqrt_ge_one hy_sqrt_ge_one
    have : (1 : ℝ) + 1 = 2 := by norm_num
    simpa [hs₁, this] using h
  have h_sum_ge_two_sqrt_three :
      (2 * Real.sqrt 3 : ℝ) ≤ s₂ := by
    have hx_inner_ge :
        (3 : ℝ) ≤ 2 + Real.sqrt x := by linarith
    have hy_inner_ge :
        (3 : ℝ) ≤ 2 + Real.sqrt y := by linarith
    have hx_bound :
        Real.sqrt 3 ≤ Real.sqrt (2 + Real.sqrt x) := by
      simpa using (Real.sqrt_le_sqrt hx_inner_ge)
    have hy_bound :
        Real.sqrt 3 ≤ Real.sqrt (2 + Real.sqrt y) := by
      simpa using (Real.sqrt_le_sqrt hy_inner_ge)
    have :
        Real.sqrt 3 + Real.sqrt 3
          ≤ Real.sqrt (2 + Real.sqrt x) + Real.sqrt (2 + Real.sqrt y) :=
      add_le_add hx_bound hy_bound
    have h_two_sqrt :
        Real.sqrt 3 + Real.sqrt 3 = 2 * Real.sqrt 3 := by ring
    have h_rhs :
        Real.sqrt (2 + Real.sqrt x) + Real.sqrt (2 + Real.sqrt y) = s₂ := by
      simp [hs₂]
    linarith
  have h_den_lower :
      (4 * Real.sqrt 3 : ℝ) ≤ s₁ * s₂ := by
    have h_nonneg₂ : 0 ≤ s₂ := (le_of_lt hs₂_pos)
    have h_step₁ :
        2 * s₂ ≤ s₁ * s₂ :=
      mul_le_mul_of_nonneg_right h_sum_ge_two h_nonneg₂
    have h_step₂ :
        (4 * Real.sqrt 3 : ℝ) ≤ 2 * s₂ := by
      have h_two_nonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
      have :=
        mul_le_mul_of_nonneg_left h_sum_ge_two_sqrt_three h_two_nonneg
      have h_left :
          (4 * Real.sqrt 3 : ℝ) = (2 : ℝ) * (2 * Real.sqrt 3) := by ring
      simpa [hs₂, two_mul, mul_comm, mul_left_comm, mul_assoc, h_left] using this
    exact h_step₂.trans h_step₁
  -- Step 4: Compare the fractions using the monotonicity of the reciprocal on positive numbers.
  have h_one_div :
      (s₁ * s₂)⁻¹ ≤ (4 * Real.sqrt 3 : ℝ)⁻¹ := by
    have :=
      one_div_le_one_div_of_le (by positivity : 0 < 4 * Real.sqrt 3) h_den_lower
    simpa using this
  -- Step 5: Multiply the reciprocal inequality by `|x - y|` to finish the Lipschitz bound.
  have h_abs_nonneg : 0 ≤ |x - y| := abs_nonneg _
  have :
      |x - y| / (s₁ * s₂)
        ≤ |x - y| / (4 * Real.sqrt 3) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left h_one_div h_abs_nonneg
  -- Step 5.1: Combine all identities and simplify back to `contractionConstant`.
  simpa [h_rewrite, contractionConstant, div_eq_mul_inv, mul_comm,
    mul_left_comm, mul_assoc, hs₁, hs₂] using this

lemma succ_diff_bound :
    ∀ n : ℕ, |f (n + 1) - f n| ≤ |f 1 - f 0| * contractionConstant ^ n := by
  -- Step 1: Use induction to propagate the contraction inequality along the sequence.
  refine Nat.rec ?base ?step
  · -- Step 1.1: The base case `n = 0` is an equality after simplifying powers.
    simp
  · -- Step 1.2: For the inductive step, combine the Lipschitz property with the inductive hypothesis.
    intro n hn
    -- Step 1.2.1: Apply the Lipschitz property to consecutive terms.
    have h_lip :
        |f (n + 2) - f (n + 1)| ≤ contractionConstant * |f (n + 1) - f n| := by
      have hx : Real.sqrt 2 ≤ f (n + 1) := sqrt_two_le_f (n + 1)
      have hy : Real.sqrt 2 ≤ f n := sqrt_two_le_f n
      simpa [f_succ] using lipschitz_update (f (n + 1)) (f n) hx hy
    -- Step 1.2.2: Substitute the inductive hypothesis and extract the new factor `contractionConstant`.
    calc
      |f (n + 2) - f (n + 1)|
          ≤ contractionConstant * |f (n + 1) - f n| := h_lip
      _ ≤ contractionConstant * (|f 1 - f 0| * contractionConstant ^ n) :=
        mul_le_mul_of_nonneg_left hn contractionConstant_nonneg
      _ = |f 1 - f 0| * contractionConstant ^ (n + 1) := by
        simp [pow_succ, mul_comm, mul_assoc]

lemma dist_succ_bound (n : ℕ) :
    dist (f n) (f (n + 1)) ≤ |f 1 - f 0| * contractionConstant ^ n := by
  -- Step 1: Translate the absolute-value control into the metric formulation on `ℝ`.
  simpa [Real.dist_eq, abs_sub_comm] using succ_diff_bound n

/-Informal Statement

If $s_{1}=\sqrt{2}$, and $s_{n+1}=\sqrt{2+\sqrt{s_{n}}} \quad(n=1,2,3, \ldots),$ prove that $\left\{s_{n}\right\}$ converges, and that $s_{n}<2$ for $n=1,2,3, \ldots$.
-/

/-Informal Proof

Since $\sqrt{2}<2$, it is manifest that if $s_n<2$, then $s_{n+1}<\sqrt{2+2}=2$. Hence it follows by induction that $\sqrt{2}<s_n<2$ for all $n$. In view of this fact,it also follows that $\left(s_n-2\right)\left(s_n+1\right)<0$ for all $n>1$, i.e., $s_n>s_n^2-2=s_{n-1}$. Hence the sequence is an increasing sequence that is bounded above (by 2 ) and so converges. Since the limit $s$ satisfies $s^2-s-2=0$, it follows that the limit is 2.
-/

theorem Rudin_exercise_3_3
  : ∃ (x : ℝ), Tendsto f atTop (𝓝 x) ∧ ∀ n, f n < 2 := by
  -- Step 1: Control successive distances with a geometric bound.
  have h_geom :
      ∀ n, dist (f n) (f (n + 1))
          ≤ |f 1 - f 0| * contractionConstant ^ n := by
    intro n
    exact dist_succ_bound n
  -- Step 2: Deduce that `(f n)` is a Cauchy sequence using the geometric estimate.
  have h_cauchy :
      CauchySeq f :=
    cauchySeq_of_le_geometric
      (r := contractionConstant) (C := |f 1 - f 0|)
      contractionConstant_lt_one h_geom
  -- Step 3: Invoke completeness of `ℝ` to produce the limit point.
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete h_cauchy
  refine ⟨x, hx, ?_⟩
  -- Step 4: Record the uniform bound `f n < 2` proved earlier.
  intro n
  exact f_lt_two n
