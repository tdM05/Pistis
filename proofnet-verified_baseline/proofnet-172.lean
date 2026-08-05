import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Suppose $f^{\prime}(x)>0$ in $(a, b)$. Prove that $f$ is strictly increasing in $(a, b)$, and let $g$ be its inverse function. Prove that $g$ is differentiable, and that $g^{\prime}(f(x))=\frac{1}{f^{\prime}(x)} \quad(a < x < b)$.
-/

/-Informal Proof

For any $c, d$ with $a<c<d<b$ there exists a point $p \in(c, d)$ such that $f(d)-f(c)=f^{\prime}(p)(d-c)>0$. Hence $f(c)<f(d)$

We know from Theorem $4.17$ that the inverse function $g$ is continuous. (Its restriction to each closed subinterval $[c, d]$ is continuous, and that is sufficient.) Now observe that if $f(x)=y$ and $f(x+h)=y+k$, we have
$$
\frac{g(y+k)-g(y)}{k}-\frac{1}{f^{\prime}(x)}=\frac{1}{\frac{f(x+h)-f(x)}{h}}-\frac{1}{f^{\prime}(x)}
$$
Since we know $\lim \frac{1}{\varphi(t)}=\frac{1}{\lim \varphi(t)}$ provided $\lim \varphi(t) \neq 0$, it follows that for any $\varepsilon>0$ there exists $\eta>0$ such that
$$
\left|\frac{1}{\frac{f(x+h)-f(x)}{h}}-\frac{1}{f^{\prime}(x)}\right|<\varepsilon
$$
if $0<|h|<\eta$. Since $h=g(y+k)-g(y)$, there exists $\delta>0$ such that $0<|h|<\eta$ if $0<|k|<\delta$. The proof is now complete.
-/


theorem Rudin_exercise_5_2 {a b : ℝ}
  {f g : ℝ → ℝ} (hf : ∀ x ∈ Set.Ioo a b, deriv f x > 0)
  (hg : g = f⁻¹) :
  StrictMonoOn f (Set.Ioo a b) ∧
  DifferentiableOn ℝ g (Set.Ioo a b) ∧
  ∀ x ∈ Set.Ioo a b, deriv g (f x) = 1 / deriv f x := by
  sorry

/-!
The Lean formalization above is false: the symbol `f⁻¹` is interpreted pointwise, so `g = f⁻¹`
really means `g x = (f x)⁻¹` for every `x`, i.e., `g` is the reciprocal of `f`, not its
functional inverse.  Taking `a = 1`, `b = 2`, and `f x = x` makes every hypothesis true
(`deriv f x = 1 > 0`, and indeed `g = 1 / ·`), yet the conclusion fails because
`deriv g (f x) = -(f x)⁻²` while `1 / deriv f x = 1`.  The mismatch comes from confusing the
algebraic inverse with the compositional inverse.
-/

def Rudin_exercise_5_2_formal : Prop :=
  ∀ (a b : ℝ) (f g : ℝ → ℝ),
    (∀ x ∈ Set.Ioo a b, deriv f x > 0) →
    g = f⁻¹ →
    StrictMonoOn f (Set.Ioo a b) ∧
      DifferentiableOn ℝ g (Set.Ioo a b) ∧
        ∀ x ∈ Set.Ioo a b, deriv g (f x) = 1 / deriv f x

theorem Rudin_exercise_5_2_neg : ¬ Rudin_exercise_5_2_formal := by
  -- Step 1: Assume (for contradiction) that the flawed formal statement is true.
  intro h
  -- Step 2: Specialize to the concrete counterexample `a = 1`, `b = 2`, `f = id`, `g = 1 / ·`.
  let a : ℝ := 1
  let b : ℝ := 2
  let f : ℝ → ℝ := fun x => x
  let g : ℝ → ℝ := fun x => (f x)⁻¹
  -- Step 3: Verify that the hypothesis on the derivative is satisfied on `(1, 2)`.
  have hf : ∀ x ∈ Set.Ioo a b, deriv f x > 0 := by
    intro x hx
    -- Step 3.1: `deriv f x = 1` for the identity map, so it is strictly positive.
    simp [f]
  -- Step 4: Observe that, by definition, `g = f⁻¹` because `f⁻¹` is pointwise inversion.
  have hg : g = f⁻¹ := by
    -- Step 4.1: Pointwise functions into a field inherit inverses elementwise.
    funext x; simp [g, f]
  -- Step 5: Extract the (false) conclusion for this specific data.
  have hcon := h a b f g hf hg
  rcases hcon with ⟨_, _, hEq⟩
  -- Step 6: Work at the interior point `x₀ = 3 / 2` of `(1, 2)`.
  let x0 : ℝ := 3 / 2
  have hx0_mem : x0 ∈ Set.Ioo a b := by
    -- Step 6.1: `3/2` lies strictly between `1` and `2`.
    constructor
    · norm_num [a, b, x0]
    · norm_num [a, b, x0]
  -- Step 7: Rewrite both sides of the derived equality at `x₀` using explicit derivatives.
  have h_left : deriv g (f x0) = -(1 / (f x0) ^ 2) := by
    -- Step 7.1: Apply the derivative of the reciprocal composed with the identity.
    have hx0_ne : f x0 ≠ 0 := by simp [f, x0]
    simp [g, f, one_div]
  have h_right : 1 / deriv f x0 = 1 := by
    -- Step 7.2: The derivative of the identity is constantly `1`.
    simp [f]
  have h_eq_value : -(1 / (f x0) ^ 2) = 1 := by
    -- Step 7.3: Combine the explicit expressions with the claimed equality.
    simpa [h_left, h_right] using hEq x0 hx0_mem
  -- Step 8: Show the obtained equality contradicts the order structure of ℝ.
  have hx0_pos : 0 < f x0 := by simp [f, x0]
  have hden_pos : 0 < (f x0) ^ 2 := sq_pos_of_pos hx0_pos
  have hneg : -(1 / (f x0) ^ 2) < 0 := by
    -- Step 8.1: The reciprocal of a positive number is positive, so its negation is negative.
    have hpos : 0 < 1 / (f x0) ^ 2 := one_div_pos.mpr hden_pos
    linarith
  -- Step 8.2: Translating the equality into `1 < 0` yields the final contradiction.
  have hneg' : (1 : ℝ) < 0 := by
    simpa using (h_eq_value ▸ hneg)
  have : ¬ (1 : ℝ) < 0 := by norm_num
  exact this hneg'

/-!
Corrected statement:
If `deriv f x > 0` on `(a, b)` and `g` is the functional inverse of `f` (i.e., `g (f x) = x`
for all `x ∈ (a, b)`), then `f` is strictly increasing on `(a, b)`, `g` is differentiable on
`f '' (a, b)`, and `deriv g (f x) = 1 / deriv f x`.
-/

theorem Rudin_exercise_5_2_corrected :
    ∀ (a b : ℝ) (f g : ℝ → ℝ),
      (∀ x ∈ Set.Ioo a b, deriv f x > 0) →
      (∀ x ∈ Set.Ioo a b, g (f x) = x) →
      StrictMonoOn f (Set.Ioo a b) ∧
        DifferentiableOn ℝ g (f '' Set.Ioo a b) ∧
          ∀ x ∈ Set.Ioo a b, deriv g (f x) = 1 / deriv f x := by
  -- Step 1: Introduce the data: interval endpoints, functions, and hypotheses.
  intro a b f g hf hleft
  -- Step 2: Establish differentiability of f on (a, b).
  -- Step 2.1: Pointwise differentiability from nonzero derivative.
  have hf_diff_at : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x := fun x hx =>
    differentiableAt_of_deriv_ne_zero (ne_of_gt (hf x hx))
  -- Step 2.2: Upgrade to DifferentiableOn.
  have hf_diff_on : DifferentiableOn ℝ f (Set.Ioo a b) :=
    fun x hx => (hf_diff_at x hx).differentiableWithinAt
  -- Step 2.3: Differentiability implies continuity on (a, b).
  have hf_cont : ContinuousOn f (Set.Ioo a b) := hf_diff_on.continuousOn
  -- Step 3: Prove f is strictly monotone on (a, b) via the mean value theorem.
  -- Since (a, b) is convex, f is continuous on it, and deriv f > 0 on its interior (which is
  -- itself since (a, b) is open), strictMonoOn_of_deriv_pos applies.
  have hmono : StrictMonoOn f (Set.Ioo a b) :=
    strictMonoOn_of_deriv_pos (convex_Ioo a b) hf_cont (by simp only [interior_Ioo]; exact hf)
  -- Step 4: Show f '' (a, b) is open.
  -- Strategy: for any f(x) in the image, find an open interval (f(c), f(d)) around it that is
  -- contained in the image, using the intermediate value theorem on a sub-interval [c, d].
  have himage_open : IsOpen (f '' Set.Ioo a b) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hx, rfl⟩
    -- Step 4.1: Pick c and d with a < c < x < d < b using density of ℝ.
    obtain ⟨c, hca, hcx⟩ := exists_between hx.1
    obtain ⟨d, hxd, hdb⟩ := exists_between hx.2
    -- Step 4.2: Record that c and d lie in (a, b).
    have hc_mem : c ∈ Set.Ioo a b := ⟨hca, lt_trans hcx (lt_trans hxd hdb)⟩
    have hd_mem : d ∈ Set.Ioo a b := ⟨lt_trans hca (lt_trans hcx hxd), hdb⟩
    -- Step 4.3: Show (f(c), f(d)) is a neighborhood of f(x) contained in f '' (a, b).
    -- f(c) < f(x) < f(d) by strict monotonicity, so f(x) ∈ (f(c), f(d)).
    refine mem_nhds_iff.mpr ⟨Set.Ioo (f c) (f d), ?_, isOpen_Ioo,
      ⟨hmono hc_mem hx hcx, hmono hx hd_mem hxd⟩⟩
    -- Step 4.4: Show (f(c), f(d)) ⊆ f '' (a, b) via the intermediate value theorem.
    -- IVT gives (f(c), f(d)) ⊆ f '' (c, d), and (c, d) ⊆ (a, b) gives the inclusion of images.
    calc Set.Ioo (f c) (f d)
        ⊆ f '' Set.Ioo c d := intermediate_value_Ioo (lt_trans hcx hxd).le
            (hf_cont.mono (Set.Icc_subset_Ioo hc_mem.1 hd_mem.2))
      _ ⊆ f '' Set.Ioo a b := Set.image_mono (Set.Ioo_subset_Ioo hc_mem.1.le hd_mem.2.le)
  -- Step 5: Derive the local right-inverse property: f(g(y)) = y for y near f(x).
  -- Since f '' (a, b) is open and contains f(x), it is a neighborhood of f(x).
  -- For any y = f(z) with z ∈ (a, b), we have f(g(y)) = f(g(f(z))) = f(z) = y.
  have hlocal : ∀ x ∈ Set.Ioo a b, ∀ᶠ y in 𝓝 (f x), f (g y) = y := fun x hx =>
    Filter.eventually_of_mem (himage_open.mem_nhds ⟨x, hx, rfl⟩)
      (fun y ⟨z, hz, hfz⟩ => by rw [← hfz, hleft z hz])
  -- Step 6: Show g is strictly monotone on f '' (a, b).
  -- If f(p) < f(q) for p, q ∈ (a, b), then p < q by strict mono of f,
  -- so g(f(p)) = p < q = g(f(q)).
  have mono_g : StrictMonoOn g (f '' Set.Ioo a b) := by
    rintro u ⟨p, hp, rfl⟩ v ⟨q, hq, rfl⟩ huv
    rw [hleft p hp, hleft q hq]
    exact (hmono.lt_iff_lt hp hq).mp huv
  -- Step 7: Prove g is continuous at each f(x) for x ∈ (a, b).
  -- We use: a strictly monotone function is continuous at a point if it maps some neighborhood
  -- to a neighborhood (StrictMonoOn.continuousAt_of_image_mem_nhds).
  -- Step 7.1: The set f '' (a, b) is a neighborhood of f(x) (since it is open, Step 4).
  -- Step 7.2: The image g '' (f '' (a, b)) ⊇ (a, b) (since g(f(z)) = z for z ∈ (a, b)),
  --   and (a, b) is a neighborhood of x = g(f(x)). So g maps nhds to nhds.
  have hg_cont_at : ∀ x ∈ Set.Ioo a b, ContinuousAt g (f x) := by
    intro x hx
    refine mono_g.continuousAt_of_image_mem_nhds
      (himage_open.mem_nhds ⟨x, hx, rfl⟩) ?_
    rw [hleft x hx]
    exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx)
      (fun z hz => ⟨f z, ⟨z, hz, rfl⟩, hleft z hz⟩)
  -- Step 8: Compute the derivative of g at f(x) using the inverse function theorem.
  -- HasDerivAt.of_local_left_inverse requires:
  --   (a) ContinuousAt g (f x)           — established in Step 7
  --   (b) HasDerivAt f (deriv f x) x     — from differentiability (Step 2), noting g(f(x)) = x
  --   (c) deriv f x ≠ 0                  — from deriv f x > 0
  --   (d) ∀ᶠ y in 𝓝 (f x), f (g y) = y — the local right-inverse (Step 5)
  -- Conclusion: HasDerivAt g (deriv f x)⁻¹ (f x).
  have hg_hasDeriv : ∀ x ∈ Set.Ioo a b, HasDerivAt g ((deriv f x)⁻¹) (f x) := by
    intro x hx
    exact HasDerivAt.of_local_left_inverse (hg_cont_at x hx)
      (by simpa [hleft x hx] using (hf_diff_at x hx).hasDerivAt)
      (ne_of_gt (hf x hx)) (hlocal x hx)
  -- Step 9: Assemble the three conclusions.
  refine ⟨hmono, fun y hy => ?_, fun x hx => ?_⟩
  -- Step 9.1: g is differentiable on f '' (a, b) — immediate from HasDerivAt (Step 8).
  · obtain ⟨x, hx, rfl⟩ := hy
    exact (hg_hasDeriv x hx).differentiableAt.differentiableWithinAt
  -- Step 9.2: deriv g (f x) = 1 / deriv f x — read off from HasDerivAt and rewrite ⁻¹ as 1/.
  simpa [one_div] using (hg_hasDeriv x hx).deriv
