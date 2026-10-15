import Mathlib

open Filter Set TopologicalSpace Function
open scoped Topology



/-Informal Statement

Let $(X, d)$ be a metric space. If $f: X \rightarrow X$ satisfies the condition $d(f(x), f(y))=d(x, y)$ for all $x, y \in X$, then $f$ is called an isometry of $X$. Show that if $f$ is an isometry and $X$ is compact, then $f$ is bijective and hence a homeomorphism.
-/

/-Informal Proof

Note that $f$ is an imbedding. It remains to prove that $f$ is surjective. Suppose it is not, and let $a \in f(X)$. Since $X$ is compact, $f(X)$ is compact and hence closed (every metric space is Hausdorff). Thus, there exists $\varepsilon>0$ such that the $\varepsilon^{-}$ neighbourhood of $a$ is contained in $X \backslash f(X)$. Set $x_1=a$, and inductively $x_{n+1}=f\left(x_n\right)$ for $n \in \mathbb{Z}_{+}$. We show that $d\left(x_n, x_m\right) \geq \varepsilon$ for $n \neq m$. Indeed, we may assume $n<m$. If $n \geq 1$, then $d\left(x_n, x_m\right)=$ $d\left(f^{-1}\left(x_n\right), f^{-1}\left(x_m\right)\right)=d\left(x_{n-1}, x_{m-1}\right)$. By induction it follows that $d\left(x_n, x_m\right)=d\left(x_{n-i}, x_{m-i}\right)$ for all $i \geq 1$, and hence $d\left(x_n, x_m\right)=d\left(a, x_{m-n}\right)=d\left(a, f\left(x_{m-n-1}\right)\right)$. Since $f\left(x_{m-n-1}\right) \in f(X)$ and $B(a, \varepsilon) \cap f(X)=\emptyset$, we have $d\left(x_n, x_m\right) \geq \varepsilon$, as claimed. Thus $\left\{x_n\right\}_{n \in \mathbb{Z}_{+}}$is a sequence with no convergent subsequence, so $X$ is not sequentially compact. This contradicts the fact that $X$ is compact. Therefore $f$ is surjective and hence a homeomorphism.
-/

theorem Munkres_exercise_28_6 {X : Type*} [MetricSpace X]
  [CompactSpace X] {f : X → X} (hf : Isometry f) :
  Continuous f ∧ Bijective f ∧ IsOpenMap f := by
  classical
  -- Step 1: establish the easy consequences of the isometry hypothesis.
  have h_cont : Continuous f := by
    -- Step 1.1: apply the standard fact that isometries are continuous.
    simpa using hf.continuous
  have h_inj : Injective f := by
    -- Step 1.2: an isometry between metric spaces is automatically injective.
    simpa using hf.injective
  -- Step 2: prove that `f` must also be surjective by contradicting compactness.
  have h_surj : Surjective f := by
    -- Step 2.1: assume `f` misses some point and choose such a point.
    classical
    by_contra h_not
    have hx₀_exists : ∃ x₀, ∀ x, f x ≠ x₀ := by
      -- Step 2.1.1: unfold the negation of surjectivity.
      simpa [Surjective, not_forall, not_exists] using h_not
    obtain ⟨x₀, hx₀⟩ := hx₀_exists
    let rangeSet : Set X := Set.range f
    have hx₀_notin : x₀ ∉ rangeSet := by
      -- Step 2.1.2: the chosen point is indeed outside the image.
      rintro ⟨x, hx⟩
      exact hx₀ x hx
    have hx₀_compl : x₀ ∈ rangeSetᶜ := by
      -- Step 2.1.3: restate the exclusion as membership in the complement.
      simpa using hx₀_notin
    -- Step 2.2: use compactness to get a positive distance from `x₀` to the image.
    have h_range_compact : IsCompact rangeSet := isCompact_range h_cont
    have h_range_closed : IsClosed rangeSet := h_range_compact.isClosed
    have hx₀_nhds : rangeSetᶜ ∈ 𝓝 x₀ :=
      h_range_closed.isOpen_compl.mem_nhds hx₀_compl
    obtain ⟨ε, ε_pos, h_ball⟩ := Metric.mem_nhds_iff.mp hx₀_nhds
    -- Step 2.3: set up the forward orbit of the missing point.
    let seq : ℕ → X := fun n => (f^[n]) x₀
    have hf_iter : ∀ n : ℕ, Isometry fun x : X => f^[n] x := by
      -- Step 2.3.1: each iterate of an isometry is an isometry.
      intro n
      induction' n with n ih
      · -- Step 2.3.1.1: the zeroth iterate is the identity.
        simpa [Function.iterate_zero] using (isometry_id : Isometry (fun x : X => x))
      · -- Step 2.3.1.2: compose the previous iterate with `f`.
        simpa [Function.iterate_succ, Function.comp] using ih.comp hf
    have h_seq_range : ∀ {n}, 0 < n → seq n ∈ rangeSet := by
      -- Step 2.3.2: all positive iterates land inside the image of `f`.
      intro n hn
      have h_ne : n ≠ 0 := Nat.ne_of_gt hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h_ne
      refine ⟨seq m, ?_⟩
      -- Step 2.3.2.1: rewrite the successor iterate explicitly.
      simp [seq, Function.iterate_succ_apply']
    have h_dist_ge : ∀ {z}, z ∈ rangeSet → ε ≤ dist x₀ z := by
      -- Step 2.3.3: points in the image stay at least `ε` away from `x₀`.
      intro z hz
      refine le_of_not_gt ?_
      intro hlt
      have hz_ball : z ∈ Metric.ball x₀ ε := by
        simpa [Metric.mem_ball, dist_comm] using hlt
      have hz_notin : z ∉ rangeSet := h_ball hz_ball
      exact hz_notin hz
    have h_dist_iter : ∀ n m, dist (seq n) (seq (n + m)) = dist (seq 0) (seq m) := by
      -- Step 2.3.4: use isometries of iterates to compare distances.
      intro n m
      have := (hf_iter n).dist_eq (seq 0) (seq m)
      simpa [seq, Function.iterate_add_apply] using this
    have h_pairwise : ∀ ⦃i j⦄, i < j → ε ≤ dist (seq i) (seq j) := by
      -- Step 2.3.5: different orbit points stay `ε` apart.
      intro i j hij
      have hpos : 0 < j - i := Nat.sub_pos_of_lt hij
      have hmem : seq (j - i) ∈ rangeSet := h_seq_range hpos
      have hsum : i + (j - i) = j := Nat.add_sub_of_le (Nat.le_of_lt hij)
      have hEq : dist (seq i) (seq j) = dist (seq 0) (seq (j - i)) := by
        simpa [hsum] using h_dist_iter i (j - i)
      have hge : ε ≤ dist (seq 0) (seq (j - i)) := h_dist_ge hmem
      simpa [hEq] using hge
    -- Step 2.4: compactness gives a convergent subsequence of `seq`.
    have h_seqcompact : IsSeqCompact (Set.univ : Set X) :=
      (isCompact_univ : IsCompact (Set.univ : Set X)).isSeqCompact
    have h_seq_mem : ∀ n, seq n ∈ (Set.univ : Set X) := by
      intro _
      simp
    obtain ⟨y, hy, hφ⟩ := h_seqcompact (x := seq) h_seq_mem
    obtain ⟨φ, hφ⟩ := hφ
    obtain ⟨hφ_mono, hφ_tendsto⟩ := hφ
    obtain ⟨N, hN⟩ :=
      Metric.tendsto_atTop.1 hφ_tendsto (ε / 2) (half_pos ε_pos)
    have h_close_N : dist (seq (φ N)) y < ε / 2 := hN N le_rfl
    have h_close_succ : dist (seq (φ (N + 1))) y < ε / 2 :=
      hN (N + 1) (Nat.le_succ _)
    have hsum_lt : dist (seq (φ N)) y + dist y (seq (φ (N + 1))) < ε := by
      have h₂ : dist y (seq (φ (N + 1))) < ε / 2 := by
        simpa [dist_comm] using h_close_succ
      simpa [add_comm, add_left_comm, add_assoc, add_halves] using
        add_lt_add h_close_N h₂
    have h_small : dist (seq (φ N)) (seq (φ (N + 1))) < ε := by
      have h_triangle := dist_triangle (seq (φ N)) y (seq (φ (N + 1)))
      exact lt_of_le_of_lt h_triangle hsum_lt
    have h_lt : φ N < φ (N + 1) := hφ_mono (Nat.lt_succ_self N)
    have h_ge : ε ≤ dist (seq (φ N)) (seq (φ (N + 1))) := h_pairwise h_lt
    exact ((not_lt_of_ge h_ge) h_small).elim
  -- Step 3: the bijectivity and topological consequences now follow.
  have h_bij : Bijective f := ⟨h_inj, h_surj⟩
  -- Step 3.1: construct an explicit inverse using the surjectivity proof.
  classical
  let g : X → X := fun y => Classical.choose (h_surj y)
  have hg_right : RightInverse g f := by
    -- Step 3.1.1: `g` sends each point to a preimage chosen by surjectivity.
    intro y
    simpa [g] using Classical.choose_spec (h_surj y)
  have hg_left : LeftInverse g f := by
    -- Step 3.1.2: injectivity upgrades the right inverse to a true inverse.
    intro x
    apply h_inj
    simpa using hg_right (f x)
  have h_inv_isom : Isometry g := hf.right_inv hg_right
  have h_inv_cont : Continuous g := h_inv_isom.continuous
  -- Step 3.2: use the continuity of the inverse to show that `f` is an open map.
  have h_open : IsOpenMap f := by
    -- Step 3.2.1: express images of open sets as preimages under the inverse.
    intro U hU
    have h_img_eq : f '' U = g ⁻¹' U := by
      ext y; constructor
      · -- Step 3.2.1.1: forward inclusion.
        rintro ⟨x, hx, rfl⟩
        have : g (f x) = x := hg_left x
        simpa [Set.mem_preimage, this]
      · -- Step 3.2.1.2: backward inclusion.
        intro hy
        have hy' : g y ∈ U := by
          simpa [Set.mem_preimage] using hy
        refine ⟨g y, hy', ?_⟩
        simpa [hg_right] using hg_right y
    -- Step 3.2.2: open sets stay open because preimages under a continuous map are open.
    have h_preimage_open : IsOpen (g ⁻¹' U) := h_inv_cont.isOpen_preimage (s := U) hU
    simpa [h_img_eq] using h_preimage_open
  -- Step 4: package the three desired properties.
  exact ⟨h_cont, h_bij, h_open⟩
