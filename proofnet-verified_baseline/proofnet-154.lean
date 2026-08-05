import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators InnerProductSpace



/-Informal Statement

If $k \geq 2$ and $\mathbf{x} \in R^{k}$, prove that there exists $\mathbf{y} \in R^{k}$ such that $\mathbf{y} \neq 0$ but $\mathbf{x} \cdot \mathbf{y}=0$
-/

/-Informal Proof

If $\mathbf{x}$ has any components equal to 0 , then $\mathbf{y}$ can be taken to have the corresponding components equal to 1 and all others equal to 0 . If all the components of $\mathbf{x}$ are nonzero, $\mathbf{y}$ can be taken as $\left(-x_2, x_1, 0, \ldots, 0\right)$. This is, of course, not true when $k=1$, since the product of two nonzero real numbers is nonzero.
-/

theorem Rudin_exercise_1_18a
  (n : ℕ)
  (h : n > 1)
  (x : EuclideanSpace ℝ (Fin n)) -- R^n
  : ∃ (y : EuclideanSpace ℝ (Fin n)), y ≠ 0 ∧ ⟪x, y⟫_ℝ = 0 := by
  classical
  -- Step 1: Record useful inequalities and fix two distinguished coordinates (0 and 1).
  have hpos : 0 < n := lt_trans Nat.zero_lt_one h
  have hone : 1 < n := h
  let i0 : Fin n := ⟨0, hpos⟩
  let i1 : Fin n := ⟨1, hone⟩
  have hi0i1 : i0 ≠ i1 := by
    intro hij
    have := congrArg Fin.val hij
    simp [i0, i1] at this
  -- Step 2: Split into the cases x = 0 and x ≠ 0.
  by_cases hx : x = 0
  · -- Step 2.1: When x = 0, pick the standard basis vector in the i0-direction.
    refine ⟨EuclideanSpace.single i0 (1 : ℝ), ?_, ?_⟩
    -- Step 2.1.1: Show this chosen vector is nonzero by inspecting its i0-coordinate.
    intro hzero
    have := congrArg (fun z => z i0) hzero
    simp [EuclideanSpace.single_apply, i0] at this
    -- Step 2.1.2: The inner product with the zero vector is automatically zero.
    simp [hx]
  · -- Step 2.2: Assume x ≠ 0 and extract a coordinate i where x has a nonzero component.
    have hxcoord : ∃ i, x i ≠ 0 := by
      by_contra h'
      push_neg at h'
      have : x = 0 := by
        ext i
        simpa [Pi.zero_apply] using h' i
      exact hx this
    obtain ⟨i, hxi⟩ := hxcoord
    -- Step 2.2.1: Choose a second coordinate j distinct from i among {i0, i1}.
    let j : Fin n := if hi : i = i0 then i1 else i0
    have hij : i ≠ j := by
      by_cases hi : i = i0
      · have hj : j = i1 := by simp [j, hi]
        simpa [hi, hj] using hi0i1
      · have hj : j = i0 := by simp [j, hi]
        simpa [hj] using hi
    -- Step 2.2.2: Build y so that only the i- and j-coordinates are possibly nonzero.
    let y := EuclideanSpace.single i (x j) - EuclideanSpace.single j (x i)
    -- Step 2.2.3: Prove that y is nonzero by looking at its j-coordinate.
    have hji : j ≠ i := Ne.symm hij
    have hyj : y j = -x i := by
      simp [y, EuclideanSpace.single_apply, hji]
    have hy_ne_zero : y ≠ 0 := by
      intro hy
      have : x i = 0 := by
        have := congrArg (fun z => z j) hy
        simpa [hyj] using this
      exact hxi this
    -- Step 2.2.4: Verify the inner product vanishes using bilinearity and the single-vector lemmas.
    refine ⟨y, hy_ne_zero, ?_⟩
    simp [y, inner_sub_right, EuclideanSpace.inner_single_right, mul_comm]
