import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

If $f$ is defined on $E$, the graph of $f$ is the set of points $(x, f(x))$, for $x \in E$. In particular, if $E$ is a set of real numbers, and $f$ is real-valued, the graph of $f$ is a subset of the plane. Suppose $E$ is compact, and prove that $f$ is continuous on $E$ if and only if its graph is compact.
-/

/-Informal Proof

Let $Y$ be the co-domain of the function $f$. We invent a new metric space $E \times Y$ as the set of pairs of points $(x, y), x \in E, y \in Y$, with the metric $\rho\left(\left(x_1, y_1\right),\left(x_2, y_2\right)\right)=d_E\left(x_1, x_2\right)+d_Y\left(y_1, y_2\right)$. The function $\varphi(x)=(x, f(x))$ is then a mapping of $E$ into $E \times Y$.

We claim that the mapping $\varphi$ is continuous if $f$ is continuous. Indeed, let $x \in X$ and $\varepsilon>0$ be given. Choose $\eta>0$ so that $d_Y(f(x), f(u))<\frac{\varepsilon}{2}$ if $d_E(x, y)<\eta$. Then let $\delta=\min \left(\eta, \frac{\varepsilon}{2}\right)$. It is easy to see that $\rho(\varphi(x), \varphi(u))<\varepsilon$ if $d_E(x, u)<\delta$. Conversely if $\varphi$ is continuous, it is obvious from the inequality $\rho(\varphi(x), \varphi(u)) \geq d_Y(f(x), f(u))$ that $f$ is continuous.

From these facts we deduce immediately that the graph of a continuous function $f$ on a compact set $E$ is compact, being the image of $E$ under the continuous mapping $\varphi$. Conversely, if $f$ is not continuous at some point $x$, there is a sequence of points $x_n$ converging to $x$ such that $f\left(x_n\right)$ does not converge to $f(x)$. If no subsequence of $f\left(x_n\right)$ converges, then the sequence $\left\{\left(x_n, f\left(x_n\right)\right\}_{n=1}^{\infty}\right.$ has no convergent subsequence, and so the graph is not compact. If some subsequence of $f\left(x_n\right)$ converges, say $f\left(x_{n_k}\right) \rightarrow z$, but $z \neq f(x)$, then the graph of $f$ fails to contain the limit point $(x, z)$, and hence is not closed. A fortiori it is not compact.
-/

theorem Rudin_exercise_4_6
  (f : ℝ → ℝ)
  (E : Set ℝ)
  (G : Set (ℝ × ℝ))
  (h₁ : IsCompact E)
  (h₂ : G = {(x, f x) | x ∈ E})
  : ContinuousOn f E ↔ IsCompact G := by
  classical
  /- Step 0: Package the graph of `f` over `E` as a reusable set `Γ`. -/
  set Γ : Set (ℝ × ℝ) := {(x, f x) | x ∈ E}
  /- Step 0.1: Identify `Γ` with the image of `E` through the map `x ↦ (x, f x)` for later use. -/
  have Γ_as_image : Γ = (fun x : ℝ => (x, f x)) '' E := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · intro hp
      rcases hp with ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  constructor
  · intro hf
    /- Step 1: Build the map `φ(x) = (x, f x)` and check it is continuous on `E`. -/
    have hφ : ContinuousOn (fun x : ℝ => (x, f x)) E := by
      intro x hx
      /- Step 1.1: `φ` is the product of the identity and `f`, so combine their continuity. -/
      have h_id : ContinuousWithinAt (fun x : ℝ => x) E x := continuousWithinAt_id
      have h_fx : ContinuousWithinAt f E x := hf x hx
      simpa using h_id.prodMk h_fx
    /- Step 1.2: Apply the image-of-compact-is-compact principle to the graph map. -/
    have hImage : IsCompact ((fun x : ℝ => (x, f x)) '' E) :=
      h₁.image_of_continuousOn hφ
    /- Step 1.3: Reinterpret the result in terms of `G` using the given equality. -/
    simpa [Γ, h₂, Γ_as_image] using hImage
  · intro hG
    /- Step 2: Translate the compactness assumption from `G` to our notation `Γ`. -/
    have hΓ : IsCompact Γ := by simpa [Γ, h₂] using hG
    /- Step 2.1: Prove pointwise continuity on `E` by showing `ContinuousWithinAt f E x` for every `x`. -/
    refine fun x hx => ?_
    /- Step 2.1.1: Reduce the filter statement to sequential convergence inside `E`. -/
    have hx_tendsto : Tendsto f (𝓝[E] x) (𝓝 (f x)) := by
      /- Step 2.1.1.1: Use the sequential criterion for countably generated filters. -/
      refine tendsto_of_seq_tendsto ?_
      intro u hu
      /- Step 2.1.2: Ensure the sequence eventually stays in `E` and discard the finite prefix. -/
      have h_mem : ∀ᶠ n : ℕ in atTop, u n ∈ E :=
        hu.eventually self_mem_nhdsWithin
      obtain ⟨N, hN⟩ := (eventually_atTop.1 h_mem)
      /- Step 2.1.2.1: Define the tail `v` that lives entirely inside `E`. -/
      let v : ℕ → ℝ := fun n => u (n + N)
      have hv_mem : ∀ n, v n ∈ E := by
        intro n
        have : N ≤ n + N := Nat.le_add_left _ _
        simpa [v] using hN (n + N) this
      /- Step 2.1.2.2: Record the convergence of the tail both within `E` and in the ambient space. -/
      have hv_tendsto : Tendsto v atTop (𝓝[E] x) := by
        simpa [v] using hu.comp (tendsto_add_atTop_nat N)
      have hv_nhds : Tendsto v atTop (𝓝 x) :=
        hv_tendsto.mono_right nhdsWithin_le_nhds
      /- Step 2.1.3: Encode the graph sequence `w n = (v n, f (v n))`. -/
      let w : ℕ → ℝ × ℝ := fun n => (v n, f (v n))
      have hw_mem : ∀ n, w n ∈ Γ := by
        intro n
        exact ⟨v n, hv_mem n, rfl⟩
      /- Step 2.1.4: Show `w` itself converges to `(x, f x)` by controlling all its subsequences. -/
      have hw_limit : Tendsto w atTop (𝓝 (x, f x)) := by
        /- Step 2.1.4.1: Use the subsequence criterion with compactness of `Γ`. -/
        refine tendsto_of_subseq_tendsto ?_
        intro ns hns
        /- Step 2.1.4.1.a: Apply compactness to `w ∘ ns` to obtain a convergent sub-subsequence. -/
        obtain ⟨p, hpΓ, φ, hφ_mono, hφ_tend⟩ :=
          hΓ.tendsto_subseq (x := fun n => w (ns n)) (by intro n; exact hw_mem (ns n))
        /- Step 2.1.4.1.b: Track the indices and first coordinates of the convergent subsequence. -/
        have hφ_atTop : Tendsto φ atTop atTop := StrictMono.tendsto_atTop hφ_mono
        have hnsφ : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ_atTop
        have hv_comp : Tendsto (fun n => v (ns (φ n))) atTop (𝓝 x) :=
          hv_nhds.comp hnsφ
        have hfst_limit :
            Tendsto (fun n => (w (ns (φ n))).1) atTop (𝓝 p.1) :=
          (continuous_fst.tendsto p).comp hφ_tend
        have hp_fst : p.1 = x :=
          tendsto_nhds_unique hfst_limit (by simpa [w] using hv_comp)
        /- Step 2.1.4.1.c: Membership in the graph forces the entire limit to be `(x, f x)`. -/
        rcases hpΓ with ⟨t, htE, rfl⟩
        have ht_eq : t = x := by simpa using hp_fst
        refine ⟨φ, ?_⟩
        simpa [w, ht_eq, Function.comp] using hφ_tend
      /- Step 2.1.5: Project the limit of `w` to control `f ∘ v`. -/
      have hv_value :
          Tendsto (fun n => f (v n)) atTop (𝓝 (f x)) :=
        (continuous_snd.tendsto (x, f x)).comp hw_limit
      /- Step 2.1.6: Remove the shift to conclude for the original sequence `u`. -/
      have : Tendsto (fun n => f (u n)) atTop (𝓝 (f x)) :=
        (tendsto_add_atTop_iff_nat (f := fun n => f (u n)) N).1 (by simpa [v] using hv_value)
      exact this
    /- Step 2.1.2: Translate the `Tendsto` statement back to `ContinuousWithinAt`. -/
    simpa [ContinuousWithinAt] using hx_tendsto
