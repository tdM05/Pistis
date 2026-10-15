import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

abbrev I : Set ℝ := Icc 0 1

/-Informal Statement

Let $X$ be completely regular, let $A$ and $B$ be disjoint closed subsets of $X$. Show that if $A$ is compact, there is a continuous function $f \colon X \rightarrow [0, 1]$ such that $f(A) = \{0\}$ and $f(B) = \{1\}$.
-/

/-Informal Proof

Since $X$ is completely regular $\forall a \in A, \exists f_a: X \rightarrow[0,1]: f_a(a)=0$ and $f_a(B)=\{1\}$. For some $\epsilon_a \in(0,1)$ we have that $U_a:=f_a^{-1}([0, \epsilon))$ is an open neighborhood of $a$ that does not intersect $B$. We therefore have an open covering $\left\{U_a \mid a \in A\right\}$ of $A$, so since $A$ is compact we have a finite subcover $\left\{U_{a_i} \mid 1 \leq i \leq m\right\}$. For each $1 \leq i \leq m$ define
$$
\begin{aligned}
\tilde{f}_{a_i}: X & \rightarrow[0,1] \\
x & \mapsto \frac{\max \left(f_{a_i}(x), \epsilon_{a_i}\right)-\epsilon_{a_i}}{1-\epsilon_{a_i}}
\end{aligned}
$$
so that $\forall x \in U_{a_i}: \tilde{f}_{a_i}(x)=0$ and $\forall x \in B, \forall 1 \leq i \leq m: \tilde{f}_{a_i}(x)=1$, and define $f:=$ $\prod_{i=1}^m \tilde{f}_{a_i}$. Then since $A \subset \cup_{i=1}^m U_{a_i}$ we have that $f(A)=\{0\}$ and also we have $f(B)=\{1\}$.
-/

theorem Munkres_exercise_33_8
  (X : Type*) [TopologicalSpace X] [CompletelyRegularSpace X]
  (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
  (hAB : Disjoint A B)
  (hAc : IsCompact A) :
  ∃ (f : X → I), Continuous f ∧ f '' A = {0} ∧ f '' B = {1} := by
  sorry

/--
The conclusion becomes impossible when `A` or `B` is empty, because
`f '' ∅ = ∅` for every map.  Taking `X = ℝ`, `A = ∅`, and `B = {0}`
produces explicit data that violate the desired conclusion.
-/
theorem Munkres_exercise_33_8_neg :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : CompletelyRegularSpace X)
      (A B : Set X) (_hA : IsClosed A) (_hB : IsClosed B)
      (_hAB : Disjoint A B) (_hAc : IsCompact A),
        ¬ ∃ f : X → I, Continuous f ∧ f '' A = {0} ∧ f '' B = {1} := by
  classical
  -- Step 1: Choose the concrete space/data that contradict the claim.
  refine ⟨ℝ, inferInstance, inferInstance, (∅ : Set ℝ), ({0} : Set ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · exact isClosed_empty
  · exact isClosed_singleton (x := (0 : ℝ))
  · simp
  · exact isCompact_empty
  -- Step 2: Show that no function on this data can satisfy the stated image conditions.
  · intro hf
    rcases hf with ⟨f, _hf_cont, hfA, _hfB⟩
    have hnonempty : (f '' (∅ : Set ℝ)).Nonempty := ⟨0, by simp [hfA]⟩
    have : (∅ : Set I).Nonempty := by simp at hnonempty
    rcases this with ⟨x, hx⟩
    exact hx.elim

/--
Corrected version: the separation conclusion holds once we explicitly
assume `A` and `B` are nonempty, so that asking for the exact images
`{0}` and `{1}` makes sense.
-/
theorem Munkres_exercise_33_8_corrected
  (X : Type*) [TopologicalSpace X] [CompletelyRegularSpace X]
  (A B : Set X) (_hA : IsClosed A) (hB : IsClosed B)
  (hAB : Disjoint A B) (hAc : IsCompact A)
  (hAn : A.Nonempty) (hBn : B.Nonempty) :
  ∃ (f : X → I), Continuous f ∧ f '' A = {0} ∧ f '' B = {1} := by
  classical
  -- Step 1: Separate each `a ∈ A` from `B` via complete regularity.
  have hAB' := Set.disjoint_left.mp hAB
  have h_aux : ∀ x : A, ∃ f : X → I, Continuous f ∧ f x = 0 ∧ EqOn f 1 B := by
    intro x
    have hxnot : (x : X) ∉ B := fun hxB => hAB' x.property hxB
    obtain ⟨f, hf_cont, hfx, hfB⟩ :=
      CompletelyRegularSpace.completely_regular (x : X) B hB hxnot
    exact ⟨f, hf_cont, hfx, hfB⟩
  choose f hf_cont hf_zero hf_one using h_aux
  -- Step 2: Build open neighborhoods on which each chosen function is small.
  set ε : ℝ := (1 / 2) with hε_def
  let U : A → Set X := fun x => {y | (f x y : ℝ) < ε}
  have hε_pos : 0 < ε := by simp [hε_def]
  have hU_open : ∀ x : A, IsOpen (U x) := by
    intro x
    have hcont : Continuous fun y : X => ((f x y : ℝ)) :=
      continuous_subtype_val.comp (hf_cont x)
    simpa [U] using hcont.isOpen_preimage (s := Set.Iio ε) isOpen_Iio
  have hU_mem : ∀ x : A, (x : X) ∈ U x := by
    intro x
    have hxval : ((f x x : I) : ℝ) = 0 := by
      simpa using congrArg Subtype.val (hf_zero x)
    have : ((f x x : I) : ℝ) < ε := by simp [hxval, hε_def]
    simpa [U] using this
  have hcover : A ⊆ ⋃ x : A, U x := by
    intro a ha
    refine Set.mem_iUnion.2 ?_
    exact ⟨⟨a, ha⟩, by simpa using hU_mem ⟨a, ha⟩⟩
  obtain ⟨t, hAt⟩ :=
    hAc.elim_finite_subcover (U := fun x : A => U x) (fun x => hU_open x) hcover
  -- Step 3: Clamp each separator so that it is zero on `U x` and one on `B`.
  let δ : ℝ := 2
  let φ : A → X → ℝ := fun x y => δ * (max ((f x y : ℝ)) ε - ε)
  have hδ_nonneg : 0 ≤ δ := by norm_num [δ]
  have hφ_cont : ∀ x : A, Continuous fun y : X => φ x y := by
    intro x
    have hval : Continuous fun y : X => ((f x y : ℝ)) :=
      continuous_subtype_val.comp (hf_cont x)
    have hconstε : Continuous fun _ : X => ε := continuous_const
    have hconstδ : Continuous fun _ : X => δ := continuous_const
    have hmax : Continuous fun y : X => max ((f x y : ℝ)) ε :=
      hval.max hconstε
    have hshift : Continuous fun y : X => max ((f x y : ℝ)) ε - ε :=
      hmax.sub hconstε
    exact hconstδ.mul hshift
  have hφ_range : ∀ x : A, ∀ y : X, 0 ≤ φ x y ∧ φ x y ≤ 1 := by
    intro x y
    rcases (f x y).property with ⟨hx0, hx1⟩
    have hnum_nonneg : 0 ≤ max ((f x y : ℝ)) ε - ε :=
      sub_nonneg.mpr (le_max_right _ _)
    have hε_le_one : ε ≤ 1 := by norm_num [hε_def]
    have hmax_le_one : max ((f x y : ℝ)) ε ≤ 1 :=
      max_le hx1 hε_le_one
    have hnum_le_half : max ((f x y : ℝ)) ε - ε ≤ 1 / 2 := by
      have h := sub_le_sub_right hmax_le_one ε
      have hrewrite : (1 : ℝ) - ε = 1 / 2 := by norm_num [hε_def]
      exact hrewrite ▸ h
    have hupper : δ * (max ((f x y : ℝ)) ε - ε) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hnum_le_half hδ_nonneg
      simpa [φ, hε_def, δ] using this
    exact ⟨mul_nonneg hδ_nonneg hnum_nonneg, hupper⟩
  have hφ_zero : ∀ {x : A} {y : X}, y ∈ U x → φ x y = 0 := by
    intro x y hy
    have hlt : (f x y : ℝ) ≤ ε := le_of_lt (by simpa [U] using hy)
    have hmax : max ((f x y : ℝ)) ε = ε := max_eq_right hlt
    simp [φ, hmax]
  have hφ_one : ∀ {x : A} {y : X}, y ∈ B → φ x y = 1 := by
    intro x y hy
    have hx : (f x y : ℝ) = 1 := by
      simpa using congrArg Subtype.val (hf_one x hy)
    have hε_le_one : ε ≤ 1 := by norm_num [hε_def]
    have hmax : max ((f x y : ℝ)) ε = (f x y : ℝ) :=
      max_eq_left (by simpa [hx] using hε_le_one)
    have hφ_eval : φ x y = δ * ((f x y : ℝ) - ε) := by simp [φ, hmax]
    have hscale : δ * ((1 : ℝ) - ε) = 1 := by norm_num [δ, hε_def]
    have hφ_eval' : φ x y = δ * (1 - ε) := by simpa [hx] using hφ_eval
    exact hφ_eval'.trans hscale
  -- Step 4: Take a finite product of the clamped functions.
  have hg_range_aux :
      ∀ s : Finset A, ∀ y : X,
        0 ≤ ∏ x ∈ s, φ x y ∧ ∏ x ∈ s, φ x y ≤ 1 := by
    classical
    intro s
    refine Finset.induction_on s (by intro y; simp)
        ?_
    intro a s ha ih y
    specialize ih y
    rcases ih with ⟨ih_nonneg, ih_le⟩
    rcases hφ_range a y with ⟨hφ_nonneg, hφ_le⟩
    constructor
    · simpa [Finset.prod_insert, ha] using mul_nonneg hφ_nonneg ih_nonneg
    · have := mul_le_mul_of_nonneg_left ih_le hφ_nonneg
      have := this.trans (by simpa [mul_one] using hφ_le)
      simpa [Finset.prod_insert, ha] using this
  let g₀ : X → ℝ := fun y => ∏ x ∈ t, φ x y
  have hg₀_range : ∀ y : X, 0 ≤ g₀ y ∧ g₀ y ≤ 1 := fun y => by
    simpa [g₀] using hg_range_aux t y
  have hg₀_cont : Continuous g₀ :=
    continuous_finset_prod _ fun x hx => hφ_cont x
  -- Step 5: Upgrade to an `I`-valued function and record its boundary values.
  let g : X → I := fun y => ⟨g₀ y, (hg₀_range y).1, (hg₀_range y).2⟩
  have hg_cont : Continuous g := hg₀_cont.subtype_mk fun y => hg₀_range y
  have hgA_zero : ∀ {a : X}, a ∈ A → g a = 0 := by
    intro a ha
    classical
    have hmem : a ∈ ⋃ x ∈ t, U x := hAt ha
    rcases Set.mem_iUnion.mp hmem with ⟨x, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hx_mem, hax⟩
    have hxzero : φ x a = 0 := hφ_zero hax
    have hprod_zero : g₀ a = 0 := by
      classical
      have hxzero' : (fun z : A => φ z a) x = 0 := by simpa using hxzero
      have := Finset.prod_eq_zero (s := t) (f := fun z : A => φ z a) hx_mem hxzero'
      simpa [g₀] using this
    apply Subtype.ext
    simp [g, hprod_zero]
  have hgB_one : ∀ {b : X}, b ∈ B → g b = 1 := by
    intro b hb
    classical
    have hprod_one : g₀ b = 1 := by
      classical
      have hxone : ∀ x ∈ t, φ x b = 1 := fun x _ => hφ_one (x := x) hb
      have := Finset.prod_eq_one (s := t) (f := fun z : A => φ z b) hxone
      simpa [g₀] using this
    apply Subtype.ext
    simp [g, hprod_one]
  -- Step 6: Leverage nonemptiness to obtain exact images `{0}` and `{1}`.
  have hA_subset_zero : g '' A ⊆ ({0} : Set I) := by
    intro z hz
    rcases hz with ⟨a, ha, rfl⟩
    simp [hgA_zero ha]
  obtain ⟨a₀, ha₀⟩ := hAn
  have h0_mem : (0 : I) ∈ g '' A := ⟨a₀, ha₀, hgA_zero ha₀⟩
  have hA_superset : ({0} : Set I) ⊆ g '' A := by
    intro z hz
    have hz0 : z = 0 := by simpa using hz
    simpa [hz0] using h0_mem
  have hA_image : g '' A = ({0} : Set I) :=
    Set.Subset.antisymm hA_subset_zero hA_superset
  have hB_subset_one : g '' B ⊆ ({1} : Set I) := by
    intro z hz
    rcases hz with ⟨b, hb, rfl⟩
    simp [hgB_one hb]
  obtain ⟨b₀, hb₀⟩ := hBn
  have h1_mem : (1 : I) ∈ g '' B := ⟨b₀, hb₀, hgB_one hb₀⟩
  have hB_superset : ({1} : Set I) ⊆ g '' B := by
    intro z hz
    have hz1 : z = 1 := by simpa using hz
    simpa [hz1] using h1_mem
  have hB_image : g '' B = ({1} : Set I) :=
    Set.Subset.antisymm hB_subset_one hB_superset
  -- Step 7: Package the constructed function with the required properties.
  exact ⟨g, hg_cont, hA_image, hB_image⟩
