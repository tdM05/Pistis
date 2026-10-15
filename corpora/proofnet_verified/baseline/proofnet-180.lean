import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

noncomputable section

namespace OrderedFinpartition

/-- The ordered finpartition with one part containing all of `Fin n`. -/
def single (n : ℕ) (hn : 0 < n) : OrderedFinpartition n where
  -- Step OFP.1: Define the unique block of the one-part ordered partition.
  length := 1
  -- Step OFP.2: The unique block has size `n`.
  partSize _ := n
  -- Step OFP.3: The block size is positive by the hypothesis `0 < n`.
  partSize_pos _ := hn
  -- Step OFP.4: The embedding of the unique block is the identity on `Fin n`.
  emb _ i := i
  -- Step OFP.5: The identity embedding is strictly monotone.
  emb_strictMono _ := strictMono_id
  -- Step OFP.6: The ordering condition on block maxima is trivial because there is one block.
  parts_strictMono := Subsingleton.strictMono _
  -- Step OFP.7: Pairwise disjointness is trivial because there are no two distinct blocks.
  disjoint := by
    intro i _ j _ hij
    have : i = j := Subsingleton.elim i j
    exact (hij this).elim
  -- Step OFP.8: The single block covers every element of `Fin n`.
  cover x := ⟨0, Set.mem_range_self x⟩

lemma sum_partSize_eq {n : ℕ} (c : OrderedFinpartition n) :
    (∑ i : Fin c.length, c.partSize i) = n := by
  -- Step OFP.9: Count the disjoint union of all parts in two ways.
  calc
    -- Step OFP.9.1: The cardinality of the sigma type of all part elements is the sum
    -- of the cardinalities of the individual parts.
    (∑ i : Fin c.length, c.partSize i) =
        Fintype.card ((i : Fin c.length) × Fin (c.partSize i)) := by
      simp [Fintype.card_sigma]
    -- Step OFP.9.2: `c.equivSigma` identifies that sigma type with `Fin n`.
    _ = Fintype.card (Fin n) := Fintype.card_congr c.equivSigma
    -- Step OFP.9.3: The cardinality of `Fin n` is `n`.
    _ = n := by simp

lemma eq_single_of_length_eq_one {n : ℕ} (hn : 0 < n) (c : OrderedFinpartition n)
    (hc : c.length = 1) : c = OrderedFinpartition.single n hn := by
  -- Step OFP.10: Record that the sum of all part sizes is `n`.
  have hsum0 := sum_partSize_eq c
  -- Step OFP.11: Unpack the ordered finpartition so the dependent fields can be rewritten.
  cases c with
  | mk length partSize partSize_pos emb emb_strictMono parts_strictMono disjoint cover =>
    -- Step OFP.11.1: Simplify the unpacked fields and replace `length` by `1`.
    dsimp at hc hsum0 ⊢
    subst length
    -- Step OFP.12: Since there is only one part and all part sizes sum to `n`, that part
    -- has size `n`.
    have hpart0 : partSize 0 = n := by
      simpa using hsum0
    -- Step OFP.13: Every index of `Fin 1` is the unique index `0`, so every part size is `n`.
    have hpart : partSize = fun _ => n := by
      funext i
      have : i = 0 := Subsingleton.elim i 0
      rw [this, hpart0]
    subst hpart
    simp only at emb emb_strictMono parts_strictMono disjoint cover ⊢
    -- Step OFP.14: For the unique block, the strictly monotone self-map `Fin n → Fin n`
    -- is the identity by the standard lower and upper bounds for strict monotone maps.
    have hval : ∀ r : Fin n, emb 0 r = r := by
      intro r
      exact le_antisymm (StrictMono.apply_le (emb_strictMono 0))
        (StrictMono.le_apply (emb_strictMono 0))
    -- Step OFP.15: Extend the pointwise identity on the unique block to equality of embeddings.
    have hemb : emb = fun _ r => r := by
      funext i r
      have hi : i = 0 := Subsingleton.elim i 0
      rw [hi, hval]
    -- Step OFP.16: With the size and embedding fields identified, the structures are equal.
    subst hemb
    rfl

lemma eq_atomic_of_length_eq {n : ℕ} (c : OrderedFinpartition n) (hc : c.length = n) :
    c = OrderedFinpartition.atomic n := by
  -- Step OFP.17: Again record the global sum of part sizes.
  have hsum0 := sum_partSize_eq c
  -- Step OFP.18: Unpack the ordered finpartition to reason directly about the fields.
  cases c with
  | mk length partSize partSize_pos emb emb_strictMono parts_strictMono disjoint cover =>
    -- Step OFP.18.1: Simplify the unpacked fields and replace `length` by `n`.
    dsimp at hc hsum0 ⊢
    subst length
    -- Step OFP.19: If there are `n` positive parts whose sizes sum to `n`, every part has
    -- size `1`.
    have hpart : partSize = fun _ => 1 := by
      funext i
      -- Step OFP.19.1: Suppose one part is not size `1`; positivity forces it to be larger.
      by_contra hne
      have hle : ∀ j : Fin n, 1 ≤ partSize j := fun j => partSize_pos j
      have hlt_i : 1 < partSize i := lt_of_le_of_ne (hle i) (Ne.symm hne)
      -- Step OFP.19.2: Then the sum of the part sizes is strictly larger than the sum of
      -- `n` many ones.
      have hlt_sum : (∑ j : Fin n, (1 : ℕ)) < ∑ j : Fin n, partSize j := by
        apply Finset.sum_lt_sum
        · intro j _
          exact hle j
        · exact ⟨i, by simp, hlt_i⟩
      -- Step OFP.19.3: But both sums are equal to `n`, contradiction.
      have hsum_one : (∑ j : Fin n, (1 : ℕ)) = n := by simp
      omega
    subst hpart
    simp only [Nat.reduceSub] at parts_strictMono emb emb_strictMono disjoint cover ⊢
    -- Step OFP.20: With singleton blocks, the map sending each block to its unique element is
    -- a strict monotone self-map of `Fin n`, hence the identity.
    have hval : ∀ m : Fin n, emb m 0 = m := by
      intro m
      exact le_antisymm (StrictMono.apply_le parts_strictMono)
        (StrictMono.le_apply parts_strictMono)
    -- Step OFP.21: Convert the pointwise identity into equality of embedding fields.
    have hemb : emb = fun m _ => m := by
      funext m r
      have : r = 0 := Subsingleton.elim r 0
      rw [this, hval]
    -- Step OFP.22: With all fields identified, the partition is the atomic partition.
    subst hemb
    rfl

end OrderedFinpartition



/-Informal Statement

Let $\Omega$ be a bounded open subset of $\mathbb{C}$, and $\varphi: \Omega \rightarrow \Omega$ a holomorphic function. Prove that if there exists a point $z_{0} \in \Omega$ such that $\varphi\left(z_{0}\right)=z_{0} \quad \text { and } \quad \varphi^{\prime}\left(z_{0}\right)=1$ then $\varphi$ is linear.
-/

/-Informal Proof

When $\Omega$ is connected, if $\varphi$ is not linear, then there exists $n \geq 2$ and $a_n \neq 0$, such that
$$
\varphi(z)=z+a_n\left(z-z_0\right)^n+O\left(\left(z-z_0\right)^{n+1}\right) .
$$
As you have noticed, by induction, it follows that for every $k \geq 1$,
$$
\varphi^k(z)=z+k a_n\left(z-z_0\right)^n+O\left(\left(z-z_0\right)^{n+1}\right) .
$$
Let $r>0$ be such that when $\left|z-z_0\right| \leq r$, then $z \in \Omega$. Then by (1),
$$
k a_n=\frac{1}{2 \pi i} \int_{\left|z-z_0\right|=r} \frac{\varphi^k(z)}{\left(z-z_0\right)^{n+1}} d z .
$$
Since $\varphi^k(\Omega) \subset \Omega$ and since $\Omega$ is bounded, there exists $M>0$, independent of $k$, such that $\left|\varphi^k\right| \leq M$ on $\Omega$. Then by (2),
$$
k\left|a_n\right| \leq M r^{-n} .
$$
Since $k$ is arbitrary, $a_n=0$, a contradiction.
-/

theorem Shakarchi_exercise_2_9
  {f : ℂ → ℂ} (Ω : Set ℂ) (b : Bornology.IsBounded Ω) (h : IsOpen Ω)
  (hf : DifferentiableOn ℂ f Ω) (z : Ω) (hz : f z = z) (h'z : deriv f z = 1) :
  ∃ (f_lin : ℂ →L[ℂ] ℂ), ∀ x ∈ Ω, f x = f_lin x := by
  sorry

/--
The formal statement above forgets the crucial hypothesis that `f` maps `Ω` to itself.
For instance, take `Ω = Metric.ball 0 1` and `f z = z + z ^ 2`.  The domain is open and
bounded, the point `z₀ = 0` satisfies `f z₀ = z₀`, and the derivative `deriv f z₀ = 1`,
yet the map is visibly nonlinear on every neighborhood of `0`.  Hence the stated
conclusion fails without the self-map requirement.
-/

theorem Shakarchi_exercise_2_9_neg :
    ∃ (Ω : Set ℂ) (_b : Bornology.IsBounded Ω) (_hΩ : IsOpen Ω) (f : ℂ → ℂ)
      (_hf : DifferentiableOn ℂ f Ω) (z : Ω) (_hz : f z = z) (_h'z : deriv f z = 1),
        ¬ ∃ (f_lin : ℂ →L[ℂ] ℂ), ∀ x ∈ Ω, f x = f_lin x := by
  classical
  -- Step 1: Choose the bounded open set `Ω` and the holomorphic function `f`.
  set Ω : Set ℂ := Metric.ball 0 1
  have hΩ_bdd : Bornology.IsBounded Ω := by
    -- Step 1.1: Boundedness follows immediately for any metric ball.
    simpa [Ω] using (Metric.isBounded_ball : Bornology.IsBounded (Metric.ball (0 : ℂ) (1 : ℝ)))
  have hΩ_open : IsOpen Ω := by
    -- Step 1.2: Openness is inherited from the metric ball structure.
    simp [Ω, isOpen_ball]
  let f : ℂ → ℂ := fun z => z + z ^ 2
  have hf_diff : Differentiable ℂ f := by
    -- Step 1.3: `f` is a sum of the identity and a polynomial, hence entire.
    simp [f]
  have hf : DifferentiableOn ℂ f Ω := hf_diff.differentiableOn
  -- Step 2: Exhibit the fixed point `z₀ = 0` in `Ω` and evaluate `f` and `deriv f` there.
  have hz_mem : (0 : ℂ) ∈ Ω := by
    -- Step 2.1: The center of the ball is always inside whenever the radius is positive.
    simp [Ω]
  let z0 : Ω := ⟨0, hz_mem⟩
  have hz : f z0 = z0 := by
    -- Step 2.2: Plugging `0` into `f` yields `0`.
    simp [f, z0]
  have h_deriv_at_zero : deriv f (0 : ℂ) = 1 := by
    -- Step 2.3: Differentiate `f z = z + z^2` at the origin.
    have h_id : HasDerivAt (fun z : ℂ => z) 1 0 := by
      -- Step 2.3.1: The derivative of the identity is `1`.
      simpa using (hasDerivAt_id (x := (0 : ℂ)))
    have h_sq : HasDerivAt (fun z : ℂ => z ^ 2) (0 : ℂ) 0 := by
      -- Step 2.3.2: `z ↦ z^2` has derivative `2z`, hence `0` at the origin.
      simpa using (hasDerivAt_pow (n := 2) (0 : ℂ))
    have h_total : HasDerivAt f (1 + 0) 0 := by
      -- Step 2.3.3: Combine the two derivatives via linearity.
      simpa [f, pow_two] using h_id.add h_sq
    -- Step 2.3.4: Turn the `HasDerivAt` fact into a `deriv` statement.
    simpa using h_total.deriv
  have h'z : deriv f z0 = 1 := by
    -- Step 2.4: Convert the previous derivative to the subtype point `z0`.
    simpa [z0] using h_deriv_at_zero
  -- Step 3: Prove that no complex-linear map can coincide with `f` on all of `Ω`.
  have h_counter : ¬ ∃ (f_lin : ℂ →L[ℂ] ℂ), ∀ x ∈ Ω, f x = f_lin x := by
    -- Step 3.1: Assume a linear map matches `f` on `Ω` and derive a contradiction.
    intro h_exist
    rcases h_exist with ⟨f_lin, hlin⟩
    -- Step 3.2: Choose two concrete points of `Ω`, namely `1/4` and `1/8`.
    let x₁ : ℂ := (1 : ℝ) / 4
    let x₂ : ℂ := (1 : ℝ) / 8
    have hx₁_mem : x₁ ∈ Ω := by
      -- Step 3.2.1: `|1/4| < 1`, so `x₁` lies in the unit disk.
      have hx₁_lt : |(1 : ℝ) / 4| < (1 : ℝ) := by norm_num
      simpa [Ω, x₁] using hx₁_lt
    have hx₂_mem : x₂ ∈ Ω := by
      -- Step 3.2.2: `|1/8| < 1`, so `x₂` also lies in the disk.
      have hx₂_lt : |(1 : ℝ) / 8| < (1 : ℝ) := by norm_num
      simpa [Ω, x₂] using hx₂_lt
    -- Step 3.3: Use linearity to relate the images of `x₁` and `x₂`.
    have hF_x₁ : f x₁ = f_lin x₁ := hlin _ hx₁_mem
    have hF_x₂ : f x₂ = f_lin x₂ := hlin _ hx₂_mem
    have hx₂_half : x₂ = ((1 : ℂ) / 2) * x₁ := by
      -- Step 3.3.1: By construction, `x₂ = (1/2) * x₁` (checked in the reals).
      have hx₂_half_real : ((1 : ℝ) / 8 : ℂ) = ((1 : ℝ) / 2 : ℂ) * ((1 : ℝ) / 4 : ℂ) := by
        -- Step 3.3.1.1: Lift the real identity to the complex numbers.
        have hx₂_real : (1 : ℝ) / 8 = (1 : ℝ) / 2 * ((1 : ℝ) / 4) := by norm_num
        exact_mod_cast hx₂_real
      simpa [x₁, x₂] using hx₂_half_real
    have h_lin_scal : f_lin x₂ = ((1 : ℂ) / 2) * f_lin x₁ := by
      -- Step 3.3.2: Apply linearity to the scalar relation above.
      simpa [hx₂_half, smul_eq_mul] using f_lin.map_smulₛₗ ((1 : ℂ) / 2) x₁
    have hx₂_eq : x₂ + x₂ ^ 2 = ((1 : ℂ) / 2) * (x₁ + x₁ ^ 2) := by
      -- Step 3.4: Translate the coincidence assumption into an explicit equality.
      calc
        x₂ + x₂ ^ 2 = f x₂ := by simp [f]
        _ = f_lin x₂ := hF_x₂
        _ = ((1 : ℂ) / 2) * f_lin x₁ := h_lin_scal
        _ = ((1 : ℂ) / 2) * f x₁ := by simp [hF_x₁]
        _ = ((1 : ℂ) / 2) * (x₁ + x₁ ^ 2) := by simp [f]
    -- Step 3.5: Evaluate both sides numerically to reach a contradiction.
    have hx₂_value : x₂ + x₂ ^ 2 = ((9 : ℝ) / 64 : ℂ) := by
      -- Step 3.5.1: Compute the left-hand side explicitly.
      norm_num [x₂, pow_two]
    have hx₁_value : ((1 : ℂ) / 2) * (x₁ + x₁ ^ 2) = ((10 : ℝ) / 64 : ℂ) := by
      -- Step 3.5.2: Compute the right-hand side explicitly.
      norm_num [x₁, pow_two]
    have hx₁_value' : (2 : ℂ)⁻¹ * (x₁ + x₁ ^ 2) = ((10 : ℝ) / 64 : ℂ) := by
      -- Step 3.5.4: Express the right-hand value using `2⁻¹` for easier rewriting.
      simpa [one_div] using hx₁_value
    have hx₂_eq' : ((9 : ℝ) / 64 : ℂ) = ((10 : ℝ) / 64 : ℂ) := by
      -- Step 3.5.3: Rewrite both sides of `hx₂_eq` numerically.
      calc
        ((9 : ℝ) / 64 : ℂ) = x₂ + x₂ ^ 2 := by
          simpa using hx₂_value.symm
        _ = (2 : ℂ)⁻¹ * (x₁ + x₁ ^ 2) := by
          simpa [one_div] using hx₂_eq
        _ = ((10 : ℝ) / 64 : ℂ) := hx₁_value'
    have hneq_real : (9 : ℝ) / 64 ≠ 10 / 64 := by norm_num
    have hneq_complex : ((9 : ℝ) / 64 : ℂ) ≠ ((10 : ℝ) / 64 : ℂ) := by
      -- Step 3.5.5: Transfer the real inequality to the complex numbers.
      exact_mod_cast hneq_real
    -- Step 3.5.6: Contradiction.
    exact hneq_complex hx₂_eq'
  refine ⟨Ω, hΩ_bdd, hΩ_open, f, hf, z0, hz, h'z, h_counter⟩

/--
Correction of `Shakarchi_exercise_2_9`:

The original formalization is missing the hypothesis `Set.MapsTo f Ω Ω`, i.e., that `φ` is a
**self-map** of the domain.  The informal statement encodes this via the notation `φ : Ω → Ω`
(codomain equals the domain).  Without this condition the statement is provably false — see
`Shakarchi_exercise_2_9_neg` above for a counterexample.

The corrected statement below keeps the domain as an arbitrary bounded open set `Ω` (faithful
to the informal statement) and adds the missing `MapsTo` hypothesis.  We also add connectivity,
which the informal proof uses ("When Ω is connected...") and which is standard in the context
of Shakarchi's book (bounded connected open sets).

Proof strategy (Cartan's uniqueness theorem, direct argument):
1. Show all iterated derivatives of `f - id` vanish at `z₀` by strong induction.
2. For each `n ≥ 2`: if all lower derivatives vanish, then `iteratedDeriv n (f^[k]) z₀ = k * aₙ`
   by the Faà di Bruno formula (all cross-terms vanish).
3. But `f^[k](Ω) ⊆ Ω` (bounded), so Cauchy's estimate bounds `iteratedDeriv n (f^[k]) z₀`
   independently of `k`.  Hence `aₙ = 0`.
4. By the identity principle (analyticity), `f = id` on all of `Ω`.
-/
theorem Shakarchi_exercise_2_9_corrected
  {f : ℂ → ℂ} (Ω : Set ℂ) (b : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
  (hconn : IsPreconnected Ω)
  (hf : DifferentiableOn ℂ f Ω)
  (h_maps : Set.MapsTo f Ω Ω)
  (z₀ : Ω) (hz : f z₀ = z₀) (h'z : deriv f z₀ = 1) :
  ∃ (f_lin : ℂ →L[ℂ] ℂ), ∀ x ∈ Ω, f x = f_lin x := by
  classical
  -- Step 1: Establish that `f` is analytic on `Ω` (holomorphic on open set ⟹ analytic).
  have hf_analytic : AnalyticOnNhd ℂ f Ω := hf.analyticOnNhd hΩ
  have hid_analytic : AnalyticOnNhd ℂ id Ω := fun z _ => analyticAt_id
  -- Step 1.1: Define g = f - id, which is analytic on Ω.
  let g : ℂ → ℂ := fun w => f w - w
  have hg_analytic : AnalyticOnNhd ℂ g Ω :=
    fun z hz => (hf_analytic z hz).sub (hid_analytic z hz)
  have hg_at : AnalyticAt ℂ g z₀ := hg_analytic _ z₀.2
  -- Step 2: Obtain a ball around z₀ contained in Ω (with closure in Ω).
  have hz₀_mem : (z₀ : ℂ) ∈ Ω := z₀.2
  obtain ⟨r, hr_pos, hr_sub⟩ : ∃ r > 0, Metric.closedBall (z₀ : ℂ) r ⊆ Ω := by
    obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.isOpen_iff.mp hΩ _ hz₀_mem
    exact ⟨ε / 2, by linarith, fun x hx => hε_sub (lt_of_le_of_lt
      (Metric.mem_closedBall.mp hx) (by linarith))⟩
  -- Step 3: Obtain a uniform bound M for ‖f^[k] w‖ on Ω, independent of k.
  --         Since f^[k](Ω) ⊆ Ω and Ω is bounded, all iterates are uniformly bounded.
  obtain ⟨M, hM⟩ : ∃ M, ∀ w ∈ Ω, ‖w‖ ≤ M := b.exists_norm_le
  -- Step 4: Show g = f - id vanishes in a neighborhood of z₀.
  --         Strategy: show analyticOrderAt g z₀ = ⊤ by proving all derivatives vanish.
  have hf_eq_id_near : f =ᶠ[𝓝 (z₀ : ℂ)] id := by
    -- Step 4.1: It suffices to show g vanishes near z₀.
    have hg_vanish : ∀ᶠ z in 𝓝 (z₀ : ℂ), g z = 0 := by
      -- Step 4.1.1: Show analyticOrderAt g z₀ = ⊤ via the iterated derivative criterion.
      rw [← analyticOrderAt_eq_top]
      rw [ENat.eq_top_iff_forall_ge]
      intro n
      -- Step 4.1.2: By `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`,
      --             it suffices to show iteratedDeriv i g z₀ = 0 for all i < n.
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg_at]
      -- Step 4.1.3: We prove ∀ i < n, iteratedDeriv i g z₀ = 0 by strong induction on n.
      --   The structure: show ∀ m, ∀ j < m, iteratedDeriv j g z₀ = 0.
      --   We prove a stronger helper and extract what we need.
      suffices hall : ∀ j, iteratedDeriv j g (z₀ : ℂ) = 0 from fun i _ => hall i
      -- Step 4.2: Prove the main claim by strong induction.
      --   Infrastructure shared across all cases:
      have h_iter_maps : ∀ k, Set.MapsTo f^[k] Ω Ω := fun k => h_maps.iterate k
      have h_iter_diff : ∀ k, DifferentiableOn ℂ f^[k] Ω := fun k => hf.iterate h_maps k
      have h_fixed_iter : ∀ k, f^[k] (z₀ : ℂ) = z₀ := by
        intro k; induction k with
        | zero => simp
        | succ k ih => simp [ih, hz]
      have hf_at : DifferentiableAt ℂ f z₀ := hf.differentiableAt (hΩ.mem_nhds hz₀_mem)
      have hf_contdiff : ContDiffAt ℂ ⊤ f z₀ := (hf_analytic _ hz₀_mem).contDiffAt
      have hfk_contdiff : ∀ k, ContDiffAt ℂ ⊤ f^[k] (z₀ : ℂ) := by
        intro k
        have : AnalyticAt ℂ f^[k] (z₀ : ℂ) := by
          exact (h_iter_diff k).analyticOnNhd hΩ _ hz₀_mem
        exact this.contDiffAt
      -- Step 4.3: Strong induction
      intro j
      induction j using Nat.strongRecOn with
      | _ j ih =>
      -- Step 4.3.1: j = 0: g(z₀) = f(z₀) - z₀ = 0.
      match j with
      | 0 => simp [g, iteratedDeriv_zero, hz]
      | 1 =>
        -- Step 4.3.2: j = 1: g'(z₀) = f'(z₀) - 1 = 0.
        simp only [g, iteratedDeriv_one]
        have : deriv (fun w => f w - w) (z₀ : ℂ) =
            deriv f (z₀ : ℂ) - deriv id (z₀ : ℂ) := by
          apply deriv_sub hf_at differentiableAt_id
        rw [this, deriv_id', h'z, sub_self]
      | (j + 2) =>
        -- Step 4.3.3: j ≥ 2. Use Cauchy bound + linear growth.
        set m := j + 2
        -- Cauchy bound on all iterates:
        have h_cauchy : ∀ k, ‖iteratedDeriv m (f^[k]) (z₀ : ℂ)‖ ≤ m.factorial * M / r ^ m := by
          intro k
          apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hr_pos
          · exact (h_iter_diff k).diffContOnCl_ball hr_sub
          · intro w hw
            exact hM _ (h_iter_maps k (hr_sub (Metric.sphere_subset_closedBall hw)))
        -- Key: iteratedDeriv m g z₀ = iteratedDeriv m f z₀ (since id has zero m-th deriv for m ≥ 2)
        have hg_eq_f : iteratedDeriv m g (z₀ : ℂ) = iteratedDeriv m f z₀ := by
          show iteratedDeriv m (fun w => f w - w) (z₀ : ℂ) = iteratedDeriv m f z₀
          have hid_contdiff : ContDiffAt ℂ ⊤ id (z₀ : ℂ) := contDiffAt_id
          have hsub : iteratedDeriv m (fun w => f w - w) (z₀ : ℂ) =
              iteratedDeriv m f (z₀ : ℂ) - iteratedDeriv m id (z₀ : ℂ) := by
            have : (fun w => f w - w) = f - id := by ext; simp [Pi.sub_apply]
            rw [this, iteratedDeriv_sub (hf_contdiff.of_le le_top) (hid_contdiff.of_le le_top)]
          rw [hsub]
          have hid_iter_zero : iteratedDeriv m id (z₀ : ℂ) = 0 := by
            rw [iteratedDeriv_id]
            simp [show m ≠ 0 from by omega, show m ≠ 1 from by omega]
          rw [hid_iter_zero, sub_zero]
        rw [hg_eq_f]
        -- Linear growth identity + Cauchy bound → iteratedDeriv m f z₀ = 0.
        -- By Faà di Bruno on f^[k+1] = f ∘ f^[k], using:
        --   (a) f^[k](z₀) = z₀ for all k
        --   (b) deriv f z₀ = 1
        --   (c) iteratedDeriv l f z₀ = 0 for 2 ≤ l < m (from ih + hg_eq_f argument)
        -- the only surviving terms in the partition sum give the recurrence:
        --   iteratedDeriv m (f^[k+1]) z₀ = iteratedDeriv m (f^[k]) z₀ + iteratedDeriv m f z₀
        -- Solving: iteratedDeriv m (f^[k]) z₀ = k * iteratedDeriv m f z₀.
        -- Combined with h_cauchy: k * ‖iteratedDeriv m f z₀‖ ≤ m! * M / r^m for all k.
        -- This forces iteratedDeriv m f z₀ = 0.
        have h_intermediate_zero : ∀ l, 2 ≤ l → l < m → iteratedDeriv l f (z₀ : ℂ) = 0 := by
          intro l hl1 hl2
          have := ih l hl2
          simp only [g] at this
          have hid_l : iteratedDeriv l id (z₀ : ℂ) = 0 := by
            rw [iteratedDeriv_id]
            simp [show l ≠ 0 from by omega, show l ≠ 1 from by omega]
          have hthis : iteratedDeriv l (fun w => f w - w) (z₀ : ℂ) = 0 := this
          have heq : (fun w => f w - w) = f - id := by ext; simp [Pi.sub_apply]
          rw [heq, iteratedDeriv_sub (hf_contdiff.of_le le_top) (contDiffAt_id.of_le le_top),
              hid_l, sub_zero] at hthis
          exact hthis
        -- The linear growth identity (the core Faà di Bruno computation):
        have h_lin : ∀ k : ℕ, iteratedDeriv m (f^[k]) (z₀ : ℂ) = k * iteratedDeriv m f z₀ := by
          intro k
          induction k with
          | zero =>
            simp only [Function.iterate_zero, Nat.cast_zero, zero_mul]
            rw [iteratedDeriv_id]
            simp [show m ≠ 0 from by omega, show m ≠ 1 from by omega]
          | succ k ihk =>
            -- f^[k+1] = f ∘ f^[k], apply Faà di Bruno
            have hcomp : f^[k + 1] = f ∘ f^[k] := Function.iterate_succ' f k
            conv_lhs => rw [hcomp]
            have hf_at_fk : ContDiffAt ℂ (↑m) f (f^[k] (z₀ : ℂ)) := by
              rw [h_fixed_iter k]; exact hf_contdiff.of_le le_top
            rw [iteratedDeriv_comp_eq_sum_orderedFinpartition
              hf_at_fk ((hfk_contdiff k).of_le le_top) (le_refl _)]
            -- In the sum ∑ c, iteratedDeriv c.length f (f^[k] z₀) * ∏ j, iteratedDeriv (c.partSize j) (f^[k]) z₀
            -- we substitute f^[k](z₀) = z₀.
            simp_rw [h_fixed_iter k]
            -- The Faà di Bruno partition sum simplification:
            -- For c : OrderedFinpartition m in the sum, exactly two partitions contribute:
            --   (1) The unique c with c.length = 1 (one part of size m):
            --       contributes iteratedDeriv 1 f z₀ * iteratedDeriv m (f^[k]) z₀
            --       = 1 * (k * iteratedDeriv m f z₀) = k * iteratedDeriv m f z₀
            --   (2) The unique c with c.length = m (atomic, all parts size 1):
            --       contributes iteratedDeriv m f z₀ * (deriv (f^[k]) z₀)^m
            --       = iteratedDeriv m f z₀ * 1 = iteratedDeriv m f z₀
            -- All other terms vanish because they have 2 ≤ c.length < m, so
            -- iteratedDeriv c.length f z₀ = 0 by h_intermediate_zero.
            -- Uniqueness of these partitions follows from: a strict mono Fin n → Fin n
            -- is the identity (StrictMono.le_apply + StrictMono.apply_le).
            -- Total = k * a + a = (k+1) * a.
            -- Step 4.3.3.1: Record that the current derivative order `m = j + 2` is positive.
            have hm_pos : 0 < m := by omega
            -- Step 4.3.3.2: Name the one-block ordered partition of `Fin m`.
            let c₁ : OrderedFinpartition m := OrderedFinpartition.single m hm_pos
            -- Step 4.3.3.3: Name the atomic ordered partition of `Fin m` into `m` singleton blocks.
            let cA : OrderedFinpartition m := OrderedFinpartition.atomic m
            -- Step 4.3.3.4: Package the summand in the Faà di Bruno formula as `term c`.
            let term : OrderedFinpartition m → ℂ := fun c =>
              iteratedDeriv c.length f (z₀ : ℂ) *
                ∏ j, iteratedDeriv (c.partSize j) (f^[k]) (z₀ : ℂ)
            -- Step 4.3.3.5: The one-block and atomic partitions are distinct because their
            -- lengths are `1` and `m`, and here `m ≥ 2`.
            have hc₁_ne_cA : c₁ ≠ cA := by
              intro h
              have hlen := congrArg OrderedFinpartition.length h
              simp [c₁, cA, OrderedFinpartition.single, OrderedFinpartition.atomic] at hlen
              omega
            -- Step 4.3.3.6: Prove that every iterate has derivative `1` at `z₀`.
            -- This will evaluate the atomic partition contribution.
            have h_deriv_iter : ∀ k : ℕ, deriv (f^[k]) (z₀ : ℂ) = 1 := by
              intro k
              induction k with
              | zero =>
                -- Step 4.3.3.6.1: The zeroth iterate is the identity, whose derivative is `1`.
                simp
              | succ k ihk =>
                -- Step 4.3.3.6.2: `f` is differentiable at `f^[k] z₀ = z₀`.
                have hdf : DifferentiableAt ℂ f (f^[k] (z₀ : ℂ)) := by
                  rw [h_fixed_iter k]
                  exact hf_contdiff.differentiableAt (by simp)
                -- Step 4.3.3.6.3: The `k`-th iterate is differentiable at `z₀`.
                have hdk : DifferentiableAt ℂ (f^[k]) (z₀ : ℂ) :=
                  (hfk_contdiff k).differentiableAt (by simp)
                -- Step 4.3.3.6.4: Apply the chain rule to `f^[k+1] = f ∘ f^[k]`, then use
                -- the fixed-point identity and the induction hypothesis.
                rw [show f^[k + 1] = f ∘ f^[k] from Function.iterate_succ' f k]
                rw [deriv_comp (z₀ : ℂ) hdf hdk, h_fixed_iter k, h'z, ihk, one_mul]
            -- Step 4.3.3.7: Show that every partition outside `{c₁, cA}` contributes zero.
            have hterm_zero : ∀ c : OrderedFinpartition m,
                c ∉ ({c₁, cA} : Finset (OrderedFinpartition m)) → term c = 0 := by
              intro c hc
              -- Step 4.3.3.7.1: Every ordered partition of a nonempty finite set has positive length.
              have hlen_pos : 0 < c.length := c.length_pos hm_pos
              -- Step 4.3.3.7.2: If `c.length = 1`, uniqueness of the one-block partition
              -- forces `c = c₁`, contradicting `c ∉ {c₁, cA}`.
              by_cases hlen_one : c.length = 1
              · have hc_eq : c = c₁ := by
                  simpa [c₁] using OrderedFinpartition.eq_single_of_length_eq_one hm_pos c hlen_one
                exact (hc (by simp [hc_eq])).elim
              -- Step 4.3.3.7.3: If `c.length = m`, uniqueness of the all-singletons partition
              -- forces `c = cA`, again contradicting `c ∉ {c₁, cA}`.
              by_cases hlen_m : c.length = m
              · have hc_eq : c = cA := by
                  simpa [cA] using OrderedFinpartition.eq_atomic_of_length_eq c hlen_m
                exact (hc (by simp [hc_eq])).elim
              -- Step 4.3.3.7.4: The remaining case has `2 ≤ c.length < m`.
              have hlen_ge_two : 2 ≤ c.length := by omega
              have hlen_lt_m : c.length < m := lt_of_le_of_ne c.length_le hlen_m
              -- Step 4.3.3.7.5: The outer derivative factor is zero by the induction
              -- hypothesis on all intermediate derivatives of `f`.
              dsimp [term]
              rw [h_intermediate_zero c.length hlen_ge_two hlen_lt_m, zero_mul]
            -- Step 4.3.3.8: Reduce the full finite sum to the two nonzero support terms.
            have hsum_support :
                ∑ c : OrderedFinpartition m, term c = term c₁ + term cA := by
              -- Step 4.3.3.8.1: The two-element support set is a subset of the universal finset.
              have hsubset :
                  ({c₁, cA} : Finset (OrderedFinpartition m)) ⊆ Finset.univ := by
                intro c _
                simp
              -- Step 4.3.3.8.2: Since all terms outside `{c₁, cA}` vanish, summing over that
              -- support set is the same as summing over all ordered finpartitions.
              have hsum_subset :
                  (∑ c ∈ ({c₁, cA} : Finset (OrderedFinpartition m)), term c) =
                    ∑ c : OrderedFinpartition m, term c := by
                exact Finset.sum_subset hsubset (by
                  intro c _ hc
                  exact hterm_zero c hc)
              -- Step 4.3.3.8.3: Evaluate the two-element support sum as `term c₁ + term cA`.
              rw [← hsum_subset, Finset.sum_pair hc₁_ne_cA]
            -- Step 4.3.3.9: Evaluate the one-block contribution.  Its outer derivative is
            -- `deriv f z₀ = 1`, and its inner derivative is handled by `ihk`.
            have hterm_c₁ : term c₁ = (k : ℂ) * iteratedDeriv m f (z₀ : ℂ) := by
              simp [term, c₁, OrderedFinpartition.single, iteratedDeriv_one, h'z, ihk]
            -- Step 4.3.3.10: Evaluate the atomic contribution.  All inner factors are
            -- first derivatives of `f^[k]` at `z₀`, hence all are `1`.
            have hterm_cA : term cA = iteratedDeriv m f (z₀ : ℂ) := by
              simp [term, cA, OrderedFinpartition.atomic, iteratedDeriv_one, h_deriv_iter]
            -- Step 4.3.3.11: Replace the original Faà di Bruno sum with the named `term` sum.
            change ∑ c : OrderedFinpartition m, term c = (k + 1 : ℕ) * iteratedDeriv m f (z₀ : ℂ)
            -- Step 4.3.3.12: Substitute the support reduction and the two evaluated terms.
            rw [hsum_support, hterm_c₁, hterm_cA]
            -- Step 4.3.3.13: Normalize the natural-number cast and finish by ring algebra:
            -- `k * a + a = (k + 1) * a`.
            rw [Nat.cast_add, Nat.cast_one]
            ring
        -- Conclude: iteratedDeriv m f z₀ = 0 from linear growth + uniform bound.
        by_contra h_ne
        have h_norm_pos : (0 : ℝ) < ‖iteratedDeriv m f (z₀ : ℂ)‖ := norm_pos_iff.mpr h_ne
        obtain ⟨k, hk⟩ : ∃ k : ℕ, m.factorial * M / r ^ m < k • ‖iteratedDeriv m f (z₀ : ℂ)‖ :=
          exists_lt_nsmul h_norm_pos _
        have h_bound := h_cauchy k
        rw [h_lin k, norm_mul, Complex.norm_natCast] at h_bound
        rw [nsmul_eq_mul] at hk
        linarith
    -- Step 4.3: Convert "g vanishes near z₀" to "f = id near z₀".
    filter_upwards [hg_vanish] with z hz
    simp [g, sub_eq_zero] at hz
    exact hz
  -- Step 5: Extend from local equality to global equality using the identity principle.
  --         Since f and id are both analytic on the preconnected open set Ω, and they
  --         agree in a neighborhood of z₀ ∈ Ω, they must agree on all of Ω.
  have hf_eq_id : Set.EqOn f id Ω :=
    hf_analytic.eqOn_of_preconnected_of_eventuallyEq hid_analytic hconn hz₀_mem hf_eq_id_near
  -- Step 6: Package the identity map as a continuous linear map and conclude.
  exact ⟨ContinuousLinearMap.id ℂ ℂ, fun x hx => by simpa using hf_eq_id hx⟩


/--
Without the `IsPreconnected` hypothesis, the corrected statement is false even with `MapsTo`.
Counterexample: Ω = B(0, 1/2) ∪ B(3, 1/2) (bounded, open, disconnected).
Define f(z) = z on B(0, 1/2) and f(z) = 6 - z on B(3, 1/2).
Then f is a holomorphic self-map with f(0) = 0 and f'(0) = 1, but f is not ℂ-linear on Ω
because any ℂ-linear map agreeing with identity near 0 must be the identity, yet f(3) = 3 ≠ 3
does not help — we use the point 3 + 1/4 where f(3 + 1/4) = 6 - (3 + 1/4) = 11/4 ≠ 3 + 1/4.
-/
theorem Shakarchi_exercise_2_9_neg_wo_preconnected :
    ∃ (Ω : Set ℂ) (_b : Bornology.IsBounded Ω) (_hΩ : IsOpen Ω) (f : ℂ → ℂ)
      (_hf : DifferentiableOn ℂ f Ω)
      (_h_maps : Set.MapsTo f Ω Ω)
      (z₀ : Ω) (_hz : f z₀ = z₀) (_h'z : deriv f z₀ = 1),
        ¬ ∃ (f_lin : ℂ →L[ℂ] ℂ), ∀ x ∈ Ω, f x = f_lin x := by
  classical
  -- Step 1: Define Ω = B(0, 1/2) ∪ B(3, 1/2), a bounded open disconnected subset of ℂ.
  set Ω : Set ℂ := Metric.ball (0 : ℂ) (1/2) ∪ Metric.ball (3 : ℂ) (1/2) with hΩ_def
  -- Step 1.1: Ω is bounded (union of two bounded sets).
  have hΩ_bdd : Bornology.IsBounded Ω :=
    Metric.isBounded_ball.union Metric.isBounded_ball
  -- Step 1.2: Ω is open (union of two open balls).
  have hΩ_open : IsOpen Ω := isOpen_ball.union isOpen_ball
  -- Step 2: Define the piecewise function f.
  -- We use: f(z) = z if z ∈ B(0, 1/2), f(z) = 6 - z if z ∈ B(3, 1/2).
  -- Since the balls are disjoint, this is well-defined.
  -- Step 2.1: Prove the two balls are disjoint (distance between centers = 3 > 1/2 + 1/2).
  have h_disj : Disjoint (Metric.ball (0 : ℂ) (1/2)) (Metric.ball (3 : ℂ) (1/2)) := by
    apply Set.disjoint_left.mpr
    intro z hz₁ hz₂
    rw [Metric.mem_ball, Complex.dist_eq] at hz₁ hz₂
    simp only [sub_zero] at hz₁
    have h3 : (3 : ℝ) ≤ ‖z‖ + ‖z - 3‖ := by
      calc (3 : ℝ) = ‖(3 : ℂ)‖ := by norm_num [Complex.norm_natCast]
        _ = ‖z + (3 - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖3 - z‖ := norm_add_le z (3 - z)
        _ = ‖z‖ + ‖z - 3‖ := by rw [norm_sub_rev]
    linarith
  -- Step 2.2: Define f piecewise.
  let f : ℂ → ℂ := fun z =>
    if z ∈ Metric.ball (0 : ℂ) (1/2) then z else 6 - z
  -- Step 2.3: Record that 0 ∈ B(0, 1/2).
  have h0_in_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (1/2) := by
    rw [Metric.mem_ball]; simp
  -- Step 3: Prove f is differentiable on Ω.
  have hf_diff : DifferentiableOn ℂ f Ω := by
    -- Step 3.1: Show differentiability pointwise for each z ∈ Ω.
    intro z hz
    rcases hz with hz_left | hz_right
    · -- Step 3.1.1: For z ∈ B(0, 1/2), f = id in a neighborhood (the open ball itself).
      have hd : DifferentiableAt ℂ f z := by
        have h_nhd : Metric.ball (0 : ℂ) (1/2) ∈ 𝓝 z :=
          isOpen_ball.mem_nhds hz_left
        have heq : f =ᶠ[𝓝 z] id :=
          Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, h_nhd, fun w hw => if_pos hw⟩
        exact differentiableAt_id.congr_of_eventuallyEq heq
      exact hd.differentiableWithinAt
    · -- Step 3.1.2: For z ∈ B(3, 1/2), f = (6 - ·) in a neighborhood.
      have hd : DifferentiableAt ℂ f z := by
        have h_nhd : Metric.ball (3 : ℂ) (1/2) ∈ 𝓝 z :=
          isOpen_ball.mem_nhds hz_right
        have heq : f =ᶠ[𝓝 z] (fun w => (6 : ℂ) - w) :=
          Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, h_nhd, fun w hw => by
            have hw_not : w ∉ Metric.ball (0 : ℂ) (1/2) :=
              fun h_in => (Set.disjoint_left.mp h_disj) h_in hw
            exact if_neg hw_not⟩
        exact ((differentiableAt_const 6).sub differentiableAt_id).congr_of_eventuallyEq heq
      exact hd.differentiableWithinAt
  -- Step 4: Prove f maps Ω to Ω.
  have hf_maps : Set.MapsTo f Ω Ω := by
    intro z hz
    rcases hz with hz_left | hz_right
    · -- Step 4.1: If z ∈ B(0, 1/2), then f(z) = z ∈ B(0, 1/2) ⊆ Ω.
      have hfz : f z = z := if_pos hz_left
      rw [hfz]
      exact Set.mem_union_left _ hz_left
    · -- Step 4.2: If z ∈ B(3, 1/2), then f(z) = 6 - z.
      --   We need ‖6 - z - 3‖ = ‖-(z - 3)‖ = ‖z - 3‖ < 1/2.
      have hz_not : z ∉ Metric.ball (0 : ℂ) (1/2) :=
        fun h_in => (Set.disjoint_left.mp h_disj) h_in hz_right
      have hfz : f z = 6 - z := if_neg hz_not
      rw [hfz]
      apply Set.mem_union_right
      rw [Metric.mem_ball, Complex.dist_eq] at hz_right ⊢
      -- Step 4.2.1: ‖6 - z - 3‖ = ‖-(z - 3)‖ = ‖z - 3‖ < 1/2.
      have h_eq : (6 : ℂ) - z - 3 = -(z - 3) := by ring
      rw [h_eq, norm_neg]
      linarith
  -- Step 5: The fixed point z₀ = 0 ∈ B(0, 1/2) ⊆ Ω.
  have hz₀_mem : (0 : ℂ) ∈ Ω := Set.mem_union_left _ h0_in_ball
  let z₀ : Ω := ⟨0, hz₀_mem⟩
  -- Step 5.1: f(z₀) = f(0) = 0 = z₀ (since 0 ∈ B(0, 1/2), the if-branch gives id).
  have hz : f (z₀ : ℂ) = (z₀ : ℂ) := by
    show f 0 = 0
    show (if (0 : ℂ) ∈ Metric.ball (0 : ℂ) (1/2) then 0 else 6 - 0) = 0
    rw [if_pos h0_in_ball]
  -- Step 5.2: deriv f z₀ = 1 (f is the identity near 0).
  have h'z : deriv f (z₀ : ℂ) = 1 := by
    -- Step 5.2.1: f agrees with id on B(0, 1/2), which is a neighborhood of 0.
    have h_eq_near : f =ᶠ[𝓝 (0 : ℂ)] id := by
      filter_upwards [isOpen_ball.mem_nhds h0_in_ball] with w hw
      exact if_pos hw
    -- Step 5.2.2: Since f = id near 0, their derivatives agree at 0.
    have hd : deriv f 0 = deriv id 0 := Filter.EventuallyEq.deriv_eq h_eq_near
    rw [hd, deriv_id']
  -- Step 6: Prove f is not ℂ-linear on Ω.
  have h_not_lin : ¬ ∃ (f_lin : ℂ →L[ℂ] ℂ), ∀ x ∈ Ω, f x = f_lin x := by
    intro ⟨f_lin, hlin⟩
    -- Step 6.1: At z = 1/4 ∈ B(0, 1/2): f(1/4) = 1/4, so f_lin(1/4) = 1/4.
    have hpt_ball : (1/4 : ℂ) ∈ Metric.ball (0 : ℂ) (1/2) := by
      rw [Metric.mem_ball]; simp; norm_num
    have hpt_mem : (1/4 : ℂ) ∈ Ω := Set.mem_union_left _ hpt_ball
    have hf_pt : f (1/4 : ℂ) = 1/4 := if_pos hpt_ball
    have hlin_pt : f_lin (1/4 : ℂ) = 1/4 := by
      have := hlin (1/4 : ℂ) hpt_mem
      rw [hf_pt] at this
      exact this.symm
    -- Step 6.2: The point 3 + 1/4 ∈ B(3, 1/2) ⊆ Ω, and f(3 + 1/4) = 6 - (3 + 1/4) = 11/4.
    have hpt3_ball : (3 + 1/4 : ℂ) ∈ Metric.ball (3 : ℂ) (1/2) := by
      rw [Metric.mem_ball]; simp; norm_num
    have hpt3_mem : (3 + 1/4 : ℂ) ∈ Ω := Set.mem_union_right _ hpt3_ball
    have hpt3_not_ball : (3 + 1/4 : ℂ) ∉ Metric.ball (0 : ℂ) (1/2) :=
      fun h_in => (Set.disjoint_left.mp h_disj) h_in hpt3_ball
    -- Step 6.3: f(3 + 1/4) = 6 - (3 + 1/4) = 11/4.
    have hf_pt3 : f (3 + 1/4 : ℂ) = 11/4 := by
      show (if (3 : ℂ) + 1/4 ∈ Metric.ball (0 : ℂ) (1/2) then _ else _) = _
      rw [if_neg hpt3_not_ball]
      ring
    -- Step 6.4: By ℂ-linearity: f_lin(3 + 1/4) = f_lin(13 • (1/4)) = 13 • f_lin(1/4) = 13/4.
    have hlin_pt3 : f_lin (3 + 1/4 : ℂ) = 13/4 := by
      have h13 : (3 + 1/4 : ℂ) = (13 : ℂ) • (1/4 : ℂ) := by
        simp only [smul_eq_mul]; ring
      rw [h13, map_smul, hlin_pt, smul_eq_mul]
      ring
    -- Step 6.5: But f(3 + 1/4) = 11/4 while f_lin(3 + 1/4) = 13/4. Contradiction.
    have h_eq : f (3 + 1/4 : ℂ) = f_lin (3 + 1/4 : ℂ) := hlin _ hpt3_mem
    rw [hf_pt3, hlin_pt3] at h_eq
    -- Step 6.5.1: 11/4 ≠ 13/4 in ℂ.
    have h_ne : (11/4 : ℂ) ≠ 13/4 := by
      intro h
      have h' : (11 : ℂ) = 13 := by linear_combination 4 * h
      have h'' : (11 : ℝ) = 13 := by
        have := Complex.ofReal_injective (show ((11 : ℝ) : ℂ) = ((13 : ℝ) : ℂ) from by
          exact_mod_cast h')
        exact this
      linarith
    exact h_ne h_eq
  -- Step 7: Assemble all components into the existential.
  exact ⟨Ω, hΩ_bdd, hΩ_open, f, hf_diff, hf_maps, z₀, hz, h'z, h_not_lin⟩
