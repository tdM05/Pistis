import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

abbrev I : Set ℝ := Icc 0 1

/-Informal Statement

Define $f_{n}:[0,1] \rightarrow \mathbb{R}$ by the equation $f_{n}(x)=x^{n}$. Show that the sequence $\left(f_{n}(x)\right)$ converges for each $x \in[0,1]$.
-/

/-Informal Proof

If $0 \leq x<1$ is fixed, then $f_n(x) \rightarrow 0$ as $n \rightarrow \infty$. As $f_n(1)=1$ for all $n, f_n(1) \rightarrow 1$. Thus $\left(f_n\right)_n$ converges to $f:[0,1] \rightarrow \mathbb{R}$ given by $f(x)=0$ if $x=0$ and $f(1)=1$. The sequence
-/

theorem Munkres_exercise_21_6a
  (f : ℕ → I → ℝ)
  (h : ∀ x n, f n x = ↑x ^ n) :
  ∀ x, ∃ y, Tendsto (λ n => f n x) atTop (𝓝 y) := by
  -- Step 1: Fix an arbitrary point `x` in the interval `I = [0, 1]`.
  intro x
  classical
  -- Step 1.1: Extract the bounds `0 ≤ x ≤ 1` from the fact that `x ∈ I`.
  have hx_mem : (x : ℝ) ∈ I := by
    simp [I]
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := (Set.mem_Icc.mp hx_mem).1
  have hxle1 : (x : ℝ) ≤ 1 := (Set.mem_Icc.mp hx_mem).2
  -- Step 2: Split the analysis into the endpoint case `x = 1` and the interior case `x ≠ 1`.
  by_cases hx1 : (x : ℝ) = 1
  · -- Step 2.1: Handle the endpoint case where `x = 1`.
    -- Step 2.1.1: Show that every term of the sequence equals the constant value `1`.
    have h_const : (fun n ↦ f n x) = fun _ : ℕ ↦ (1 : ℝ) := by
      funext n
      simp [h, hx1]
    -- Step 2.1.2: Conclude by the constant sequence convergence lemma.
    refine ⟨1, ?_⟩
    simp [h_const]
  · -- Step 2.2: Handle the interior case where `x ≠ 1`, so in fact `x < 1`.
    -- Step 2.2.1: Upgrade `x ≤ 1` and `x ≠ 1` to the strict inequality `x < 1`.
    have hxlt1 : (x : ℝ) < 1 := lt_of_le_of_ne hxle1 hx1
    -- Step 2.2.2: Identify the sequence explicitly as the power sequence `n ↦ (x : ℝ) ^ n`.
    have h_pow : (fun n ↦ f n x) = fun n : ℕ ↦ (x : ℝ) ^ n := by
      funext n
      simp [h]
    -- Step 2.2.3: Apply the standard limit theorem for powers with base in `[0, 1)`.
    refine ⟨0, ?_⟩
    simpa [h_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hxlt1 :
        Tendsto (fun n : ℕ ↦ (x : ℝ) ^ n) atTop (𝓝 (0 : ℝ)))
