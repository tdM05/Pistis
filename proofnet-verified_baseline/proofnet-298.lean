import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

noncomputable section

/-Informal Statement

Show that $\mathbb{R} \times \mathbb{R}$ in the dictionary order topology is metrizable.
-/

/-Informal Proof

The dictionary order topology on $\mathbb{R} \times \mathbb{R}$ is the same as the product topology $\mathbb{R}_d \times \mathbb{R}$, where $\mathbb{R}_d$ denotes $\mathbb{R}$ with the discrete topology. We know that $\mathbb{R}_d$ and $\mathbb{R}$ are metrisable. Thus, it suffices to show that the product of two metrisable spaces is metrisable.
So let $X$ and $Y$ be metrisable spaces, with metrics $d$ and $d^{\prime}$ respectively. On $X \times Y$, define
$$
\rho(x \times y, w \times z)=\max \left\{d(x, w), d^{\prime}(y, z)\right\} .
$$
Then $\rho$ is a metric on $X \times Y$; it remains to prove that it induces the product topology on $X \times Y$. If $B_d\left(x, r_1\right) \times B_d\left(y, r_2\right)$ is a basis element for the product space $X \times Y$, and $r=\min \left\{r_1, r_2\right\}$, then $x \times y \in B_\rho(x \times y, r) \subset B_d\left(x, r_1\right) \times B_d\left(y, r_2\right)$, so the product topology is coarser than the $\rho$-topology. Conversely, if $B_\rho(x \times y, \delta)$ is a basis element for the $\rho$-topology, then $x \times y \in B_d(x, \delta) \times B_{d^{\prime}}(y, \delta) \subset$ $B_\rho(x \times y, \delta)$, so the product topology is finer than the $\rho$-topology. It follows that both topologies are equal, so the product space $X \times Y$ is metrisable.
-/

/-- Lex `(a, b) < (a, c)` reduces to `b < c` (helper). -/
private lemma lex_lt_same_fst {a b c : ℝ} (h : b < c) :
    (toLex (a, b) : ℝ ×ₗ ℝ) < toLex (a, c) := by
  rw [Prod.Lex.lt_iff]; exact Or.inr ⟨rfl, h⟩

/-- The dictionary order topology on `ℝ ×ₗ ℝ` is metrizable.
We exhibit a compatible metric: distance is `min |Δy| 1` within a fiber `{x} × ℝ`,
and `1` between distinct fibers. This metric induces exactly the order topology
because order-basic open sets `Ioo l u` and metric balls have the same form
inside each fiber. -/
theorem Munkres_exercise_20_2
  [TopologicalSpace (ℝ ×ₗ ℝ)] [OrderTopology (ℝ ×ₗ ℝ)]
  : MetrizableSpace (ℝ ×ₗ ℝ) := by
  -- The candidate distance.
  let d : ℝ ×ₗ ℝ → ℝ ×ₗ ℝ → ℝ := fun p q =>
    if (ofLex p).1 = (ofLex q).1 then min |(ofLex p).2 - (ofLex q).2| 1 else 1
  -- Metric axioms.
  have d_self : ∀ x, d x x = 0 := by
    intro x
    simp only [d, if_pos rfl, sub_self, abs_zero]
    exact min_eq_left zero_le_one
  have d_comm : ∀ x y, d x y = d y x := by
    intro x y
    simp only [d]
    by_cases h : (ofLex x).1 = (ofLex y).1
    · rw [if_pos h, if_pos h.symm, abs_sub_comm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have d_tri : ∀ x y z, d x z ≤ d x y + d y z := by
    intro x y z
    simp only [d]
    have habs_tri : |(ofLex x).2 - (ofLex z).2| ≤
        |(ofLex x).2 - (ofLex y).2| + |(ofLex y).2 - (ofLex z).2| := by
      have h : (ofLex x).2 - (ofLex z).2
          = ((ofLex x).2 - (ofLex y).2) + ((ofLex y).2 - (ofLex z).2) := by ring
      rw [h]; exact abs_add_le _ _
    have hA : (0 : ℝ) ≤ min |(ofLex x).2 - (ofLex y).2| 1 :=
      le_min (abs_nonneg _) zero_le_one
    have hB : (0 : ℝ) ≤ min |(ofLex y).2 - (ofLex z).2| 1 :=
      le_min (abs_nonneg _) zero_le_one
    -- Truncated metric on ℝ: min |·| 1 satisfies the triangle inequality.
    have trunc_tri : min |(ofLex x).2 - (ofLex z).2| 1
        ≤ min |(ofLex x).2 - (ofLex y).2| 1 + min |(ofLex y).2 - (ofLex z).2| 1 := by
      by_cases hxy_le : |(ofLex x).2 - (ofLex y).2| ≤ 1
      · by_cases hyz_le : |(ofLex y).2 - (ofLex z).2| ≤ 1
        · rw [min_eq_left hxy_le, min_eq_left hyz_le]
          calc min |(ofLex x).2 - (ofLex z).2| 1
              ≤ |(ofLex x).2 - (ofLex z).2| := min_le_left _ _
            _ ≤ _ := habs_tri
        · push_neg at hyz_le
          rw [min_eq_left hxy_le, min_eq_right hyz_le.le]
          have h1 : min |(ofLex x).2 - (ofLex z).2| 1 ≤ 1 := min_le_right _ _
          have h2 : (0 : ℝ) ≤ |(ofLex x).2 - (ofLex y).2| := abs_nonneg _
          linarith
      · push_neg at hxy_le
        rw [min_eq_right hxy_le.le]
        have h1 : min |(ofLex x).2 - (ofLex z).2| 1 ≤ 1 := min_le_right _ _
        linarith
    by_cases hxz : (ofLex x).1 = (ofLex z).1
    · rw [if_pos hxz]
      by_cases hxy : (ofLex x).1 = (ofLex y).1
      · have hyz : (ofLex y).1 = (ofLex z).1 := hxy.symm.trans hxz
        rw [if_pos hxy, if_pos hyz]
        exact trunc_tri
      · have hyz : (ofLex y).1 ≠ (ofLex z).1 :=
          fun h => hxy (hxz.trans h.symm)
        rw [if_neg hxy, if_neg hyz]
        have h1 : min |(ofLex x).2 - (ofLex z).2| 1 ≤ 1 := min_le_right _ _
        linarith
    · rw [if_neg hxz]
      by_cases hxy : (ofLex x).1 = (ofLex y).1
      · have hyz : (ofLex y).1 ≠ (ofLex z).1 :=
          fun h => hxz (hxy.trans h)
        rw [if_pos hxy, if_neg hyz]
        linarith
      · rw [if_neg hxy]
        by_cases hyz : (ofLex y).1 = (ofLex z).1
        · rw [if_pos hyz]; linarith
        · rw [if_neg hyz]; linarith
  -- (No `d_zero` needed: we build a pseudo-metric, then upgrade via T0.)
  -- Topology agreement: order-open ↔ metric-ball-friendly.
  have d_topo : ∀ s : Set (ℝ ×ₗ ℝ), IsOpen s ↔
      ∀ x ∈ s, ∃ ε > 0, ∀ y, d x y < ε → y ∈ s := by
    intro s
    rw [isOpen_iff_mem_nhds]
    refine forall₂_congr fun x _ => ?_
    rw [mem_nhds_iff_exists_Ioo_subset]
    constructor
    · -- Forward: an `Ioo l u` neighborhood gives a small metric ball.
      rintro ⟨l, u, ⟨hlx, hxu⟩, hsub⟩
      have hlx' := Prod.Lex.lt_iff.mp hlx
      have hxu' := Prod.Lex.lt_iff.mp hxu
      -- Helper: shrink a candidate ε to ensure ball ⊆ Ioo l u.
      -- A point y with same first coord as x and |Δy| < ε satisfies l < y if either
      -- (lr < xr) or (lr = xr ∧ ε ≤ xs - ls); similarly for the upper end.
      -- Provide existence of `εl, εu > 0` capturing each side.
      have εl_exists : ∃ εl > (0 : ℝ), ∀ ys : ℝ,
          (ofLex x).2 - εl < ys →
          (toLex (ofLex l) : ℝ ×ₗ ℝ) < toLex ((ofLex x).1, ys) := by
        rcases hlx' with hlt | ⟨heq, hlt⟩
        · refine ⟨1, zero_lt_one, ?_⟩
          intro ys _
          rw [Prod.Lex.toLex_lt_toLex]
          exact Or.inl hlt
        · refine ⟨(ofLex x).2 - (ofLex l).2, by linarith, ?_⟩
          intro ys hys
          rw [Prod.Lex.toLex_lt_toLex]
          exact Or.inr ⟨heq, by linarith⟩
      have εu_exists : ∃ εu > (0 : ℝ), ∀ ys : ℝ,
          ys < (ofLex x).2 + εu →
          (toLex ((ofLex x).1, ys) : ℝ ×ₗ ℝ) < toLex (ofLex u) := by
        rcases hxu' with hlt | ⟨heq, hlt⟩
        · refine ⟨1, zero_lt_one, ?_⟩
          intro ys _
          rw [Prod.Lex.toLex_lt_toLex]
          exact Or.inl hlt
        · refine ⟨(ofLex u).2 - (ofLex x).2, by linarith, ?_⟩
          intro ys hys
          rw [Prod.Lex.toLex_lt_toLex]
          exact Or.inr ⟨heq, by linarith⟩
      obtain ⟨εl, hεl_pos, hεl_safe⟩ := εl_exists
      obtain ⟨εu, hεu_pos, hεu_safe⟩ := εu_exists
      let ε : ℝ := min 1 (min εl εu)
      have hε_pos : 0 < ε := lt_min zero_lt_one (lt_min hεl_pos hεu_pos)
      have hε_le_one : ε ≤ 1 := min_le_left _ _
      have hε_le_εl : ε ≤ εl := le_trans (min_le_right _ _) (min_le_left _ _)
      have hε_le_εu : ε ≤ εu := le_trans (min_le_right _ _) (min_le_right _ _)
      refine ⟨ε, hε_pos, ?_⟩
      intro y hy
      apply hsub
      -- Force the first coordinate.
      have hy_fst : (ofLex x).1 = (ofLex y).1 := by
        by_contra hne
        simp only [d, if_neg hne] at hy
        linarith
      simp only [d, if_pos hy_fst] at hy
      have hy_abs : |(ofLex x).2 - (ofLex y).2| < ε := by
        rcases le_or_gt |(ofLex x).2 - (ofLex y).2| 1 with hcase | hcase
        · rwa [min_eq_left hcase] at hy
        · rw [min_eq_right hcase.le] at hy; linarith
      have hy_diff := abs_lt.mp hy_abs
      have hys_lo : (ofLex x).2 - εl < (ofLex y).2 := by linarith
      have hys_hi : (ofLex y).2 < (ofLex x).2 + εu := by linarith
      have hl_lt : (toLex (ofLex l) : ℝ ×ₗ ℝ) < toLex ((ofLex x).1, (ofLex y).2) :=
        hεl_safe (ofLex y).2 hys_lo
      have lt_u : (toLex ((ofLex x).1, (ofLex y).2) : ℝ ×ₗ ℝ) < toLex (ofLex u) :=
        hεu_safe (ofLex y).2 hys_hi
      have rewrite_l : (toLex (ofLex l) : ℝ ×ₗ ℝ) = l := toLex_ofLex l
      have rewrite_u : (toLex (ofLex u) : ℝ ×ₗ ℝ) = u := toLex_ofLex u
      have rewrite_y : (toLex ((ofLex x).1, (ofLex y).2) : ℝ ×ₗ ℝ) = y := by
        have h1 : ((ofLex x).1, (ofLex y).2) = ofLex y :=
          Prod.ext hy_fst rfl
        rw [h1, toLex_ofLex]
      rw [rewrite_l, rewrite_y] at hl_lt
      rw [rewrite_y, rewrite_u] at lt_u
      exact ⟨hl_lt, lt_u⟩
    · -- Backward: a metric ball gives an `Ioo l u` neighborhood.
      rintro ⟨ε, hε, hball⟩
      let ε' : ℝ := min ε 1 / 2
      have hε'_pos : 0 < ε' :=
        div_pos (lt_min hε zero_lt_one) (by norm_num)
      have hε'_le_one : ε' ≤ 1 := by
        have h1 : min ε 1 ≤ 1 := min_le_right _ _
        have : ε' = min ε 1 / 2 := rfl
        linarith
      have hε'_lt_ε : ε' < ε := by
        have h1 : min ε 1 ≤ ε := min_le_left _ _
        have hpos : 0 < min ε 1 := lt_min hε zero_lt_one
        have : ε' = min ε 1 / 2 := rfl
        linarith
      refine ⟨toLex ((ofLex x).1, (ofLex x).2 - ε'),
              toLex ((ofLex x).1, (ofLex x).2 + ε'), ⟨?_, ?_⟩, ?_⟩
      · -- toLex (xr, xs - ε') < x
        rw [Prod.Lex.lt_iff]
        simp only [ofLex_toLex]
        right
        refine ⟨?_, by linarith⟩
        trivial
      · -- x < toLex (xr, xs + ε')
        rw [Prod.Lex.lt_iff]
        simp only [ofLex_toLex]
        right
        refine ⟨?_, by linarith⟩
        trivial
      · intro y hy
        obtain ⟨hl_y, hy_u⟩ := hy
        have hl_y' : (ofLex x).1 < (ofLex y).1
            ∨ (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 - ε' < (ofLex y).2 := by
          have h : (toLex ((ofLex x).1, (ofLex x).2 - ε') : ℝ ×ₗ ℝ) < toLex (ofLex y) := by
            rw [toLex_ofLex]; exact hl_y
          have := (Prod.Lex.toLex_lt_toLex
            (x := ((ofLex x).1, (ofLex x).2 - ε')) (y := ofLex y)).mp h
          exact this
        have hy_u' : (ofLex y).1 < (ofLex x).1
            ∨ (ofLex y).1 = (ofLex x).1 ∧ (ofLex y).2 < (ofLex x).2 + ε' := by
          have h : (toLex (ofLex y) : ℝ ×ₗ ℝ) < toLex ((ofLex x).1, (ofLex x).2 + ε') := by
            rw [toLex_ofLex]; exact hy_u
          have := (Prod.Lex.toLex_lt_toLex
            (x := ofLex y) (y := ((ofLex x).1, (ofLex x).2 + ε'))).mp h
          exact this
        have hy_fst : (ofLex y).1 = (ofLex x).1 := by
          rcases hl_y' with h1 | ⟨h1, _⟩
          · rcases hy_u' with h2 | ⟨h2, _⟩
            · exact absurd (lt_trans h1 h2) (lt_irrefl _)
            · exact h2
          · exact h1.symm
        have hy_lo : (ofLex x).2 - ε' < (ofLex y).2 := by
          rcases hl_y' with h1 | ⟨_, h1⟩
          · exact absurd hy_fst.symm (ne_of_lt h1)
          · exact h1
        have hy_hi : (ofLex y).2 < (ofLex x).2 + ε' := by
          rcases hy_u' with h2 | ⟨_, h2⟩
          · exact absurd hy_fst (ne_of_lt h2)
          · exact h2
        apply hball
        simp only [d, if_pos hy_fst.symm]
        have habs_lt : |(ofLex x).2 - (ofLex y).2| < ε' := by
          rw [abs_lt]; exact ⟨by linarith, by linarith⟩
        have : min |(ofLex x).2 - (ofLex y).2| 1 = |(ofLex x).2 - (ofLex y).2| :=
          min_eq_left (by linarith)
        rw [this]; linarith
  -- Package as a `PseudoMetricSpace` whose topology is definitionally the given one;
  -- the `T0Space` half of `MetrizableSpace` follows from `OrderTopology` (a linear-order
  -- order topology is Hausdorff, hence T0).
  letI pms : PseudoMetricSpace (ℝ ×ₗ ℝ) :=
    PseudoMetricSpace.ofDistTopology d d_self d_comm d_tri d_topo
  infer_instance
