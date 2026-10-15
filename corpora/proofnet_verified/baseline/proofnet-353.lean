import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset Set
open scoped BigOperators



/-Informal Statement

Prove that every continuous open mapping of $R^{1}$ into $R^{1}$ is monotonic.
-/

/-Informal Proof

Suppose $f$ is continuous and not monotonic, say there exist points $a<b<c$ with $f(a)<f(b)$, and $f(c)<f(b)$. Then the maximum value of $f$ on the closed interval $[a, c]$ is assumed at a point $u$ in the open interval $(a, c)$. If there is also a point $v$ in the open interval $(a, c)$ where $f$ assumes its minimum value on $[a, c]$, then $f(a, c)=[f(v), f(u)]$. If no such point $v$ exists, then $f(a, c)=(d, f(u)]$, where $d=\min (f(a), f(c))$. In either case, the image of $(a, c)$ is not open.
-/

theorem Rudin_exercise_4_15 {f : ℝ → ℝ}
  (hf : Continuous f) (hof : IsOpenMap f) :
  Monotone f := by
  sorry


/-
Step 0 (Explanation):
Lean's `Monotone` predicate only captures the nondecreasing direction, while the informal
statement accepted both orientations.  The map `x ↦ -x` is continuous and open yet strictly
decreasing, so it witnesses the failure of the formalized goal above.
-/

theorem Rudin_exercise_4_15_neg :
    ¬ (∀ f : ℝ → ℝ, Continuous f → IsOpenMap f → Monotone f) := by
  classical
  -- Step 1: Introduce the decreasing homeomorphism `g x = -x`.
  let g : ℝ → ℝ := fun x => -x
  -- Step 2: `g` is continuous by `continuous_neg`.
  have hg_cont : Continuous g := by
    simpa [g] using (continuous_neg : Continuous fun x : ℝ => -x)
  -- Step 3: `g` is open because negation is a homeomorphism of `ℝ`.
  have hg_open : IsOpenMap g := by
    simpa [g] using (Homeomorph.neg ℝ).isOpenMap
  -- Step 4: `g` is not monotone (it is antitone).
  have hg_notMono : ¬ Monotone g := by
    intro hg
    have h₀₁ : (0 : ℝ) ≤ 1 := by norm_num
    have := hg h₀₁
    have : (0 : ℝ) ≤ (-1 : ℝ) := by simpa [g] using this
    exact (by norm_num : ¬ ((0 : ℝ) ≤ (-1 : ℝ))) this
  -- Step 5: Apply the quantified statement to `g` and reach a contradiction.
  refine fun h => hg_notMono ?_
  exact h g hg_cont hg_open

section

open scoped Classical

/-
Step 0 (Corrected statement):
The informal statement's "monotonic" covers both the non-decreasing and non-increasing
orientations, whereas Lean's `Monotone` captures only the former.  The faithful
formalization is therefore `Monotone f ∨ Antitone f`.

Step 1.  We show that a continuous open map `f : ℝ → ℝ` has no local maximum: if it did
at some `c`, an open neighborhood `U` of `c` would be mapped by `f` into `(-∞, f c]`;
but `f '' U` is open and contains `f c`, hence must contain points strictly greater
than `f c`, a contradiction.

Step 2.  The same argument rules out local minima.

Step 3.  If `f a = f b` with `a < b`, the topological Rolle theorem
(`exists_isLocalExtr_Ioo`) yields a local extremum in `(a, b)`, contradicting Steps
1–2.  Hence `f` is injective.

Step 4.  A continuous injective `f : ℝ → ℝ` is strictly monotone or strictly antitone
by `Continuous.strictMono_of_inj`.  Weakening strict monotonicity to monotonicity
finishes the proof.
-/
theorem Rudin_exercise_4_15_corrected {f : ℝ → ℝ}
    (hf : Continuous f) (hof : IsOpenMap f) :
    Monotone f ∨ Antitone f := by
  -- Step 1: A continuous open map has no local maximum.
  have no_local_max : ∀ c : ℝ, ¬ IsLocalMax f c := by
    intro c hmax
    -- Step 1.1: Unfold the local-max hypothesis to an eventually-in-neighborhood form.
    have hev : ∀ᶠ x in 𝓝 c, f x ≤ f c := hmax
    -- Step 1.2: Extract an open neighborhood `U ∋ c` on which `f y ≤ f c`.
    obtain ⟨U, hU_le, hU_open, hcU⟩ := eventually_nhds_iff.mp hev
    -- Step 1.3: `f '' U` is open (since `f` is an open map) and contains `f c`.
    have hopen_image : IsOpen (f '' U) := hof U hU_open
    have hmem : f c ∈ f '' U := ⟨c, hcU, rfl⟩
    -- Step 1.4: An open set in ℝ containing `f c` contains a ball around `f c`.
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen_image (f c) hmem
    have hd2pos : (0 : ℝ) < δ / 2 := by linarith
    -- Step 1.5: The point `f c + δ/2` lies in this ball.
    have hmemb : f c + δ / 2 ∈ Metric.ball (f c) δ := by
      rw [Metric.mem_ball, Real.dist_eq,
          show f c + δ / 2 - f c = δ / 2 from by ring, abs_of_pos hd2pos]
      linarith
    -- Step 1.6: Pull back to a point `y ∈ U` with `f y = f c + δ/2 > f c`, a contradiction.
    obtain ⟨y, hyU, hyeq⟩ := hball hmemb
    have hy_le : f y ≤ f c := hU_le y hyU
    linarith
  -- Step 2: A continuous open map has no local minimum (dual of Step 1).
  have no_local_min : ∀ c : ℝ, ¬ IsLocalMin f c := by
    intro c hmin
    have hev : ∀ᶠ x in 𝓝 c, f c ≤ f x := hmin
    obtain ⟨U, hU_ge, hU_open, hcU⟩ := eventually_nhds_iff.mp hev
    have hopen_image : IsOpen (f '' U) := hof U hU_open
    have hmem : f c ∈ f '' U := ⟨c, hcU, rfl⟩
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen_image (f c) hmem
    have hd2pos : (0 : ℝ) < δ / 2 := by linarith
    have hmemb : f c - δ / 2 ∈ Metric.ball (f c) δ := by
      rw [Metric.mem_ball, Real.dist_eq,
          show f c - δ / 2 - f c = -(δ / 2) from by ring, abs_neg, abs_of_pos hd2pos]
      linarith
    obtain ⟨y, hyU, hyeq⟩ := hball hmemb
    have hy_ge : f c ≤ f y := hU_ge y hyU
    linarith
  -- Step 3: Prove `f` is injective using the topological Rolle theorem.
  have hinj : Function.Injective f := by
    intro a b hfab
    by_contra hne
    -- Step 3.1: Without loss of generality consider both orderings `a < b` and `b < a`.
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- Step 3.2 (a < b): a local extremum in `(a, b)` contradicts Steps 1–2.
      obtain ⟨c, _hc_mem, hc_extr⟩ :=
        exists_isLocalExtr_Ioo hlt hf.continuousOn hfab
      rcases hc_extr with hmin | hmax
      · exact no_local_min c hmin
      · exact no_local_max c hmax
    · -- Step 3.3 (b < a): same argument with the roles of `a` and `b` swapped.
      obtain ⟨c, _hc_mem, hc_extr⟩ :=
        exists_isLocalExtr_Ioo hgt hf.continuousOn hfab.symm
      rcases hc_extr with hmin | hmax
      · exact no_local_min c hmin
      · exact no_local_max c hmax
  -- Step 4: A continuous injective `ℝ → ℝ` is strictly monotone or strictly antitone,
  -- hence (weakening strict to non-strict) monotone or antitone.
  exact (hf.strictMono_of_inj hinj).imp StrictMono.monotone StrictAnti.antitone

end
