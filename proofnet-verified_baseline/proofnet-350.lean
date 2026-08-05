import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Show that there exist a set $E \subset \mathbb{R}$ and a real continuous function $f$ defined on $E$, such that there does not exist a continuous real function $g$ on $\mathbb{R}$ such that $g(x)=f(x)$ for all $x \in E$.
-/

/-Informal Proof

Let $E:=(0,1)$, and define $f(x):=1 / x$ for all $x \in E$. If $f$ has a continuous extension $g$ to $\mathbb{R}$, then $g$ is continuous on $[-1,1]$, and therefore bounded by the intermediate value theorem. However, $f$ is not bounded in any neighborhood of $x=0$, so therefore $g$ is not bounded either, a contradiction.
-/

theorem Rudin_exercise_4_5b
  : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧
  (¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x) := by
  classical
  -- Step 1: Fix witnesses `E := (0, 1)` and `f x := x⁻¹`.
  refine ⟨Set.Ioo (0 : ℝ) 1, (fun x => x⁻¹), ?_, ?_⟩
  -- Step 2: `f` is continuous on `E` because inversion is continuous away from zero.
  have hsubset : Set.Ioo (0 : ℝ) 1 ⊆ {x : ℝ | x ≠ 0} := by
    intro x hx
    exact ne_of_gt hx.1
  have hcontFull :
      ContinuousOn (fun x : ℝ => x⁻¹) {x : ℝ | x ≠ 0} := by
    simpa using (continuousOn_inv₀ : ContinuousOn (fun x : ℝ => x⁻¹) {x : ℝ | x ≠ 0})
  have hcontE : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Ioo (0 : ℝ) 1) :=
    hcontFull.mono hsubset
  · simpa using hcontE
  · -- Step 3: Assume a continuous extension `g` on `ℝ` exists and derive a contradiction.
    intro hExt
    rcases hExt with ⟨g, hg_cont, hg_agree⟩
    -- Step 3.1: Bound `|g|` on the compact set `K := [-1, 1]`.
    let K : Set ℝ := Set.Icc (-1 : ℝ) 1
    have hK_compact : IsCompact K := isCompact_Icc
    have hK_nonempty : K.Nonempty := by
      refine ⟨0, ?_⟩
      simp [K]
    have hcont_abs : ContinuousOn (fun x : ℝ => |g x|) K :=
      (continuous_abs.comp hg_cont).continuousOn
    obtain ⟨x₀, hx₀K, hx₀_bound⟩ :=
      hK_compact.exists_isMaxOn hK_nonempty hcont_abs
    set B : ℝ := |g x₀|
    have hbound : ∀ x ∈ K, |g x| ≤ B := by
      intro x hx
      have := hx₀_bound hx
      simpa [B] using this
    -- Step 3.2: Pick a natural number `N` with `N > B` and `N ≥ 3`.
    obtain ⟨N, hN⟩ := exists_nat_gt (max B 2)
    have hNB : B < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
    have hNtwo : (2 : ℝ) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
    have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans (by norm_num : (0 : ℝ) < 2) hNtwo
    have hNgt_one : (1 : ℝ) < (N : ℝ) := lt_trans (by norm_num : (1 : ℝ) < 2) hNtwo
    -- Step 3.3: Define `x := 1 / N`, which belongs to both `E` and `K`.
    let x : ℝ := (N : ℝ)⁻¹
    have hx_pos : 0 < x := by
      simpa [x] using inv_pos.mpr hNpos
    have hx_le_half : x ≤ (1 / 2 : ℝ) := by
      have htwo_pos : 0 < (2 : ℝ) := by norm_num
      have htwo_le : (2 : ℝ) ≤ (N : ℝ) := le_of_lt hNtwo
      simpa [x] using one_div_le_one_div_of_le htwo_pos htwo_le
    have hx_lt_one : x < 1 := lt_of_le_of_lt hx_le_half (by norm_num)
    have hx_mem_E : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx_pos, hx_lt_one⟩
    have hx_mem_K : x ∈ K := by
      refine ⟨?_, (le_of_lt hx_lt_one)⟩
      have hx_nonneg : (0 : ℝ) ≤ x := le_of_lt hx_pos
      exact (by norm_num : (-1 : ℝ) ≤ 0).trans hx_nonneg
    -- Step 3.4: Evaluate `g` at `x` and compare with the compactness bound.
    have hx_val : g x = (N : ℝ) := by
      have := (hg_agree x hx_mem_E).symm
      simpa [x] using this
    have hx_abs : |g x| = (N : ℝ) := by
      have : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
      simp [hx_val, abs_of_nonneg this]
    have hx_le : (N : ℝ) ≤ B := by
      have := hbound x hx_mem_K
      simpa [B, hx_abs]
    -- Step 3.5: `N` was chosen larger than `B`, giving the contradiction `N < N`.
    have hB_lt : B < (N : ℝ) := hNB
    exact (lt_irrefl (N : ℝ)) (lt_of_le_of_lt hx_le hB_lt)
