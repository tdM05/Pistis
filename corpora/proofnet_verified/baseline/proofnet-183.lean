import Mathlib

open Complex Function Metric Finset
open scoped BigOperators Topology Bornology



/-Informal Statement

Show that there is no holomorphic function $f$ in the unit disc $D$ that extends continuously to $\partial D$ such that $f(z) = 1/z$ for $z \in \partial D$.
-/

/-Informal Proof

Consider $g(r)=\int_{|z|=r} f(z) d z$. Cauchy theorem implies that $g(r)=0$ for all $r<1$. Now since $\left.f\right|_{\partial D}=1 / z$ we have $\lim _{r \rightarrow 1} \int_{|z|=r} f(z) d z=\int_{|z|=1} \frac{1}{z} d z=\frac{2}{\pi i} \neq 0$. Contradiction.
-/

theorem Shakarchi_exercise_3_22 (D : Set ℂ) (hD : D = ball 0 1) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f D) (hfc : ContinuousOn f (closure D)) :
    ¬ ∀ z ∈ (sphere (0 : ℂ) 1), f z = 1 / z := by
  classical
  -- Step 1: Assume, towards a contradiction, that the boundary condition holds everywhere.
  intro hboundary
  -- Step 2: Record the geometric facts about the unit disk needed later (boundedness and frontier).
  have hbounded : Bornology.IsBounded D := by
    simpa [hD] using (Metric.isBounded_ball (x := (0 : ℂ)) (r := (1 : ℝ)))
  have hfrontier : frontier D = sphere (0 : ℂ) 1 := by
    simp [hD, frontier_ball (0 : ℂ) (by simp : (1 : ℝ) ≠ 0)]
  -- Step 3: Package regularity data for f and for the identity map, then build g(z)=z·f(z).
  let g : ℂ → ℂ := fun z => z * f z
  have hfDiff : DiffContOnCl ℂ f D := ⟨hf, hfc⟩
  have hid : DiffContOnCl ℂ (fun z : ℂ => z) D := (differentiable_id.diffContOnCl)
  have hgDiff : DiffContOnCl ℂ g D := by
    -- Step 3.1: Apply the smul version of DiffContOnCl to obtain smoothness and continuity of g.
    simpa [g] using (DiffContOnCl.smul (s := D) hid hfDiff)
  have hconst : DiffContOnCl ℂ (fun _ : ℂ => (1 : ℂ)) D :=
    diffContOnCl_const
  -- Step 4: Show that g agrees with the constant function 1 on the boundary (sphere) of the disk.
  have hEqFrontier : Set.EqOn g (fun _ : ℂ => (1 : ℂ)) (frontier D) := by
    intro z hz
    -- Step 4.1: Translate membership in the frontier to membership in the unit sphere.
    have hz' : z ∈ sphere (0 : ℂ) 1 := by simpa [hfrontier] using hz
    -- Step 4.2: Use the boundary hypothesis to compute g(z) explicitly.
    have hz_ne : z ≠ 0 := by
      have hz_norm : ‖z‖ = 1 := by
        simpa [sphere, dist_eq_norm] using hz'
      intro hz0
      simp [hz0] at hz_norm
    have hfz : f z = 1 / z := hboundary z hz'
    simp [g, hfz, hz_ne] 
  -- Step 5: Extend the boundary equality to the whole closed disk via the maximum modulus principle.
  have hEqClosure : Set.EqOn g (fun _ : ℂ => (1 : ℂ)) (closure D) :=
    eqOn_closure_of_eqOn_frontier hbounded hgDiff hconst hEqFrontier
  -- Step 6: Evaluate the equality at 0 (which lies in the interior) and derive the contradiction.
  have hzero_mem : (0 : ℂ) ∈ D := by
    have : (0 : ℂ) ∈ ball (0 : ℂ) (1 : ℝ) :=
      by
        simp [mem_ball_self (show (0 : ℝ) < (1 : ℝ) from zero_lt_one)]
    simp [hD, this]
  have hzero_closure : (0 : ℂ) ∈ closure D := subset_closure hzero_mem
  have hzero_eq : g 0 = (1 : ℂ) := hEqClosure hzero_closure
  simp [g] at hzero_eq
