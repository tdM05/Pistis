import Mathlib

open Complex Filter Function Metric Finset Set
open scoped BigOperators Topology



/-Informal Statement

Suppose $f$ is continuous in a region $\Omega$. Prove that any two primitives of $f$ (if they exist) differ by a constant.
-/

/-Informal Proof

Suppose $F_1$ and $F_2$ are primitives of $F$. Then $(F_1-F_2)^\prime = f - f = 0$, therefore $F_1$ and $F_2$ differ by a constant.
-/

theorem Shakarchi_exercise_1_26
  (f F₁ F₂ : ℂ → ℂ) (Ω : Set ℂ) (h0 : Nonempty Ω) (h1 : IsOpen Ω) (h2 : IsConnected Ω) (hf : ContinuousOn f Ω)
  (hF₁ : DifferentiableOn ℂ F₁ Ω) (hF₂ : DifferentiableOn ℂ F₂ Ω)
  (hdF₁ : ∀ x ∈ Ω, deriv F₁ x = f x) (hdF₂ : ∀ x ∈ Ω, deriv F₂ x = f x)
  : ∃ c : ℂ, ∀ x, F₁ x = F₂ x + c := by
  sorry

/-
Why the formalized statement is false:
Step 1: work on the region Ω := {z : ℂ | ‖z‖ < 1}, which is open, connected, and nonempty.
Step 2: choose f := 0, F₁ := 0, and F₂ := (fun z => if ‖z‖ < 1 then 0 else z); inside Ω all three functions
       are constant 0, so F₁ and F₂ are primitives of f over Ω.
Step 3: evaluate the alleged global equality F₁ = F₂ + c at z = 0 and z = 1. From z = 0 we deduce c = 0,
       while from z = 1 we get 0 = 1, which is absurd. Hence the quantified conclusion fails.
-/

namespace Proofnet179

noncomputable section

def counterexampleΩ : Set ℂ := Metric.ball 0 1

def counterexample_f : ℂ → ℂ := fun _ => 0

def counterexampleF₁ : ℂ → ℂ := fun _ => 0

def counterexampleF₂ : ℂ → ℂ := fun z => if ‖z‖ < 1 then 0 else z

theorem Shakarchi_exercise_1_26_neg :
    ¬ (∀ (f F₁ F₂ : ℂ → ℂ) (Ω : Set ℂ),
        Nonempty Ω → IsOpen Ω → IsConnected Ω →
        ContinuousOn f Ω → DifferentiableOn ℂ F₁ Ω → DifferentiableOn ℂ F₂ Ω →
        (∀ x ∈ Ω, deriv F₁ x = f x) → (∀ x ∈ Ω, deriv F₂ x = f x) →
        ∃ c : ℂ, ∀ x, F₁ x = F₂ x + c) := by
  classical
  -- Step 1: Assume the (incorrect) universal statement and aim for a contradiction.
  intro h
  -- Step 2: Record the basic topological properties of Ω = {z | ‖z‖ < 1}.
  have hΩ_nonempty : Nonempty counterexampleΩ := by
    -- Step 2.1: Exhibit 0 as a point of the ball.
    refine ⟨0, ?_⟩
    simp [counterexampleΩ]
  have hΩ_open : IsOpen counterexampleΩ := by
    -- Step 2.2: Use the standard fact that open balls are open.
    simp [counterexampleΩ]
  have hΩ_connected : IsConnected counterexampleΩ := by
    -- Step 2.3: Open balls in ℂ are connected.
    simpa [counterexampleΩ] using
      (isConnected_ball (E := ℂ) (x := (0 : ℂ)) (r := (1 : ℝ)) zero_lt_one)
  -- Step 3: Verify the analytic hypotheses for the chosen counterexample functions.
  have hf : ContinuousOn counterexample_f counterexampleΩ := by
    -- Step 3.1: ContinuousOn for constant functions is immediate.
    simpa [counterexample_f] using
      (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℂ)) counterexampleΩ)
  have hF₁ : DifferentiableOn ℂ counterexampleF₁ counterexampleΩ := by
    -- Step 3.2: F₁ is the constant-zero function, hence differentiable everywhere.
    change DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) counterexampleΩ
    exact
      (differentiableOn_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
        (s := counterexampleΩ) (c := (0 : ℂ)))
  have hF₂ : DifferentiableOn ℂ counterexampleF₂ counterexampleΩ := by
    -- Step 3.3: On Ω the function F₂ coincides with the constant zero function.
    have hConst :
        DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) counterexampleΩ :=
      (differentiableOn_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
        (s := counterexampleΩ) (c := (0 : ℂ)))
    refine hConst.congr ?_
    intro z hz
    -- Step 3.3.1: Inside the open ball the “if” branch is active, so F₂ z = 0.
    have hz' : ‖z‖ < 1 := by simpa [counterexampleΩ] using hz
    simp [counterexampleF₂, hz']
  have hdF₁ : ∀ x ∈ counterexampleΩ, deriv counterexampleF₁ x = counterexample_f x := by
    -- Step 3.4: The derivative of the constant-zero function is zero everywhere.
    intro x hx
    change deriv (fun _ : ℂ => (0 : ℂ)) x = 0
    simp
  have hF₂_eq_zero :
      counterexampleΩ.EqOn counterexampleF₂ (fun _ : ℂ => (0 : ℂ)) := by
    -- Step 3.5: Record explicitly that F₂ and the zero function agree on Ω.
    intro z hz
    have hz' : ‖z‖ < 1 := by simpa [counterexampleΩ] using hz
    simp [counterexampleF₂, hz']
  have hdF₂ : ∀ x ∈ counterexampleΩ, deriv counterexampleF₂ x = counterexample_f x := by
    -- Step 3.6: Use the previous equality and openness of Ω to transfer derivatives.
    intro x hx
    have hderiv_eq :=
      (Set.EqOn.deriv (𝕜 := ℂ) (F := ℂ) hF₂_eq_zero hΩ_open) hx
    simpa [counterexample_f] using hderiv_eq
  -- Step 4: Apply the assumed theorem to obtain a global constant c.
  obtain ⟨c, hc⟩ :=
    h counterexample_f counterexampleF₁ counterexampleF₂ counterexampleΩ hΩ_nonempty hΩ_open
      hΩ_connected hf hF₁ hF₂ hdF₁ hdF₂
  -- Step 5: Evaluate the equality at z = 0 to deduce c = 0.
  have hc_zero : c = 0 := by
    -- Step 5.1: Simplify the conclusion at the origin, which lies in Ω.
    have h0 := hc 0
    have : 0 = c := by
      simpa [counterexampleF₁, counterexampleF₂, counterexampleΩ] using h0
    simpa using this.symm
  -- Step 6: Evaluate at z = 1 (which lies outside Ω) to contradict c = 0.
  have hcontr : (0 : ℂ) = 1 := by
    -- Step 6.1: Plug z = 1 into the supposed global equality and use the previous step.
    have h1 := hc 1
    simp [counterexampleF₁, counterexampleF₂, hc_zero] at h1
  -- Step 7: The impossible equality 0 = 1 gives the contradiction.
  exact zero_ne_one hcontr

/-
Corrected version: the same hypotheses only guarantee that F₁ and F₂ differ by a constant on the
region Ω itself (the domain where the primitives are compared). Globally extending Ω can fail, so
the quantifier in the conclusion must be restricted to x ∈ Ω.
-/

theorem Shakarchi_exercise_1_26_corrected :
    ∀ (f F₁ F₂ : ℂ → ℂ) (Ω : Set ℂ),
      Nonempty Ω → IsOpen Ω → IsConnected Ω →
      ContinuousOn f Ω → DifferentiableOn ℂ F₁ Ω → DifferentiableOn ℂ F₂ Ω →
      (∀ x ∈ Ω, deriv F₁ x = f x) → (∀ x ∈ Ω, deriv F₂ x = f x) →
      ∃ c : ℂ, ∀ x ∈ Ω, F₁ x = F₂ x + c := by
  classical
  -- Step 1: Introduce arbitrary data satisfying the hypotheses.
  intro f F₁ F₂ Ω hΩ_nonempty hΩ_open hΩ_connected hf hF₁ hF₂ hdF₁ hdF₂
  -- Step 2: Convert connectedness into the preconnectedness needed by the library lemma.
  have hΩ_preconnected : IsPreconnected Ω := hΩ_connected.isPreconnected
  -- Step 3: Show that the derivatives of F₁ and F₂ agree pointwise on Ω.
  have hderiv_eq : Ω.EqOn (deriv F₁) (deriv F₂) := by
    intro z hz
    -- Step 3.1: Rewrite both derivatives through the shared integrand f.
    have h₁ := hdF₁ z hz
    have h₂ := hdF₂ z hz
    simp [h₁, h₂]
  -- Step 4: Apply the analytic uniqueness lemma to obtain the desired constant.
  obtain ⟨c, hc⟩ :=
    hΩ_open.exists_eq_add_of_deriv_eq hΩ_preconnected hF₁ hF₂ hderiv_eq
  -- Step 5: Read the equality off as an explicit formula on Ω.
  refine ⟨c, ?_⟩
  intro x hx
  -- Step 5.1: The EqOn statement exactly gives F₁ x = F₂ x + c for each x ∈ Ω.
  simpa using hc hx

end

end Proofnet179
