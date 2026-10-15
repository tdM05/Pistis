import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Let $X$ be a metric space in which every infinite subset has a limit point. Prove that $X$ is separable.
-/

/-Informal Proof

We observe that if the process of constructing $x_j$ did not terminate, the result would be an infinite set of points $x_j, j=1,2, \ldots$, such that $d\left(x_i, x_j\right) \geq \delta$ for $i \neq j$. It would then follow that for any $x \in X$, the open ball $B_{\frac{\delta}{2}}(x)$ contains at most one point of the infinite set, hence that no point could be a limit point of this set, contrary to hypothesis. Hence $X$ is totally bounded, i.e., for each $\delta>0$ there is a finite set $x_1, \ldots, x_{N\delta}$such that $X=\bigcup_{j / 1}^{N\delta} B_\delta\left(x_j\right)$

Let $x_{n_1}, \ldots, x_{n N_n}$ be such that $X=\bigcup_{j / 1}^{N_n} B_{\frac{1}{n}}\left(x_{n j}\right), n=1,2, \ldots$ We claim that $\left\{x_{n j}: 1 \leq j \leq N_n ; n=1,2, \ldots\right\}$ is a countable dense subset of $X$. Indeed
25
if $x \in X$ and $\delta>0$, then $x \in B_{\frac{1}{n}}\left(x_{n j}\right)$ for some $x_{n j}$ for some $n>\frac{1}{\delta}$, and hence $d\left(x, x_{n j}\right)<\delta$. By definition, this means that $\left\{x_{n j}\right\}$ is dense in $X$.
-/

theorem Rudin_exercise_2_24 {X : Type*} [MetricSpace X]
  (hX : ∀ (A : Set X), Infinite A → ∃ (x : X), x ∈ closure A) :
  SeparableSpace X := by
  sorry

/-
The stated hypothesis only claims that every infinite subset has a point in its closure. Since any
element of an infinite set already lies in its own closure, the condition is vacuous. Consequently,
non-separable metric spaces trivially satisfy it. We now formalize this failure via an explicit
counterexample and then prove the corrected version with a genuine limit-point requirement.
-/

namespace Exercise224

open Classical

/-! ### Counterexample: an uncountable discrete metric space -/

/-- A copy of `ℝ` equipped with the discrete metric. -/
structure RealDisc : Type where
  val : ℝ
deriving Inhabited

noncomputable instance : DecidableEq RealDisc :=
  Classical.decEq _

namespace RealDisc

instance : Coe RealDisc ℝ := ⟨RealDisc.val⟩

@[simp] lemma coe_mk (x : ℝ) : (RealDisc.mk x : ℝ) = x := rfl
@[simp] lemma mk_coe (x : RealDisc) : RealDisc.mk x = x := by cases x; rfl

noncomputable instance : Dist RealDisc :=
  ⟨fun x y => if x = y then 0 else 1⟩

@[simp] lemma dist_eq (x y : RealDisc) :
    dist x y = if x = y then 0 else 1 :=
rfl

lemma dist_nonneg' {x y : RealDisc} : 0 ≤ dist x y := by
  classical
  by_cases h : x = y
  · simp [dist_eq, h]
  · simp [dist_eq, h]

noncomputable instance : MetricSpace RealDisc where
  dist := dist
  dist_self x := by
    classical
    simp [dist_eq]
  eq_of_dist_eq_zero := by
    classical
    intro x y hxy
    by_contra hne
    have := hxy
    simp [dist_eq, hne] at this
  dist_comm := by
    classical
    intro x y
    by_cases h : x = y
    · simp [dist_eq, h]
    · have hy : y ≠ x := by
        intro hyx
        exact h hyx.symm
      simp [dist_eq, h, hy]
  dist_triangle := by
    classical
    intro x y z
    by_cases hxz : x = z
    ·
      have hx : 0 ≤ dist x y := dist_nonneg'
      have hz : 0 ≤ dist y z := dist_nonneg'
      have : 0 ≤ dist x y + dist y z := add_nonneg hx hz
      simpa [dist_eq, hxz] using this
    · have hxz' : dist x z = 1 := by simp [dist_eq, hxz]
      have hcases : x ≠ y ∨ y ≠ z := by
        by_contra hcontra
        push_neg at hcontra
        rcases hcontra with ⟨hxy, hyz⟩
        exact hxz (hxy.trans hyz)
      have hsum : (1 : ℝ) ≤ dist x y + dist y z := by
        cases hcases with
        | inl hxy =>
            have hxy' : dist x y = 1 := by simp [dist_eq, hxy]
            have hyz' : 0 ≤ dist y z := dist_nonneg'
            have : 1 ≤ 1 + dist y z := by
              simpa using add_le_add_left hyz' 1
            simpa [hxy', add_comm] using this
        | inr hyz =>
            have hyz' : dist y z = 1 := by simp [dist_eq, hyz]
            have hxy' : 0 ≤ dist x y := dist_nonneg'
            have : 1 ≤ dist x y + 1 := by
              simpa [add_comm] using add_le_add_right hxy' 1
            simpa [hyz', add_comm] using this
      simpa [hxz'] using hsum

lemma dist_eq_zero_iff {x y : RealDisc} : dist x y = 0 ↔ x = y := by
  classical
  constructor
  · intro h
    by_contra hne
    have : dist x y = 1 := by simp [dist_eq, hne]
    simp [this] at h
  · intro h
    simp [h]

lemma dist_eq_one_of_ne {x y : RealDisc} (h : x ≠ y) : dist x y = 1 := by
  classical
  simp [dist_eq, h]

lemma dist_lt_half_iff_eq {x y : RealDisc}
    (h : dist x y < (1 / 2 : ℝ)) : x = y := by
  classical
  by_contra hne
  have : dist x y = 1 := dist_eq_one_of_ne hne
  have : (1 : ℝ) < 1 / 2 := by simpa [this] using h
  norm_num at this

lemma dense_subset_eq_univ {s : Set RealDisc} (hs : Dense s) : s = Set.univ := by
  classical
  ext x
  constructor
  · intro _; trivial
  · intro _
    have hx : x ∈ closure s := by simp [hs.closure_eq]
    obtain ⟨y, hy, hxy⟩ :=
      Metric.mem_closure_iff.1 hx (1 / 2) (by norm_num)
    have : y = x := dist_lt_half_iff_eq (by simpa [dist_comm] using hxy)
    simpa [this] using hy

lemma not_separable : ¬SeparableSpace RealDisc := by
  classical
  intro hsep
  rcases hsep.exists_countable_dense with ⟨s, hs_count, hs_dense⟩
  have hs_eq : s = (Set.univ : Set RealDisc) := dense_subset_eq_univ hs_dense
  have hcountRD : (Set.univ : Set RealDisc).Countable := by
    simpa [hs_eq] using hs_count
  have hcountR :
      (Set.univ : Set ℝ).Countable := by
    have himage :=
      hcountRD.image (fun x : RealDisc => (x : ℝ))
    have hrange :
        ((fun x : RealDisc => (x : ℝ)) '' (Set.univ : Set RealDisc)) =
          (Set.univ : Set ℝ) := by
      ext y
      constructor
      · intro _; trivial
      · intro _
        exact ⟨⟨y⟩, Set.mem_univ _, rfl⟩
    simpa [hrange] using himage
  exact Cardinal.not_countable_real hcountR

lemma assumption_trivial {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Infinite A) : ∃ x : X, x ∈ closure A := by
  classical
  rcases hA.nonempty with ⟨x, hx⟩
  exact ⟨x, subset_closure hx⟩

end RealDisc

open Exercise224

/-- Negation of the flawed formal statement. -/
lemma separable_of_ulift {α : Type*} [TopologicalSpace α]
    (h : SeparableSpace (ULift α)) : SeparableSpace α := by
  classical
  -- Step 1: start from a countable dense subset upstairs.
  rcases h.exists_countable_dense with ⟨s, hs_count, hs_dense⟩
  -- Step 2: push the set down via the homeomorphism `ULift`.
  refine ⟨⟨(fun x : ULift α => x.down) '' s, hs_count.image _, ?_⟩⟩
  have hclosure :
      closure ((fun x : ULift α => x.down) '' s) =
        (fun x : ULift α => x.down) '' closure s :=
    (Homeomorph.ulift.image_closure s).symm
  have hs_closure : closure s = (Set.univ : Set (ULift α)) := hs_dense.closure_eq
  -- Step 3: record that the downward map hits every point of `α`.
  have hrange :
      Set.range (fun x : ULift α => x.down) = (Set.univ : Set α) := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      exact ⟨ULift.up y, rfl⟩
  have hclosureRangeSet :
      closure ((fun x : ULift α => x.down) '' s) =
        (fun x : ULift α => x.down) '' (Set.univ : Set (ULift α)) := by
    have := congrArg (fun t : Set (ULift α) => (fun x : ULift α => x.down) '' t) hs_closure
    simpa [hclosure] using this
  have hclosureRange :
      closure ((fun x : ULift α => x.down) '' s) =
        Set.range (fun x : ULift α => x.down) := by
    simpa [Set.image_univ] using hclosureRangeSet
  have hclosureUniv :
      closure ((fun x : ULift α => x.down) '' s) = (Set.univ : Set α) :=
    hclosureRange.trans hrange
  -- Step 4: conclude density downstairs.
  simp [Dense, hclosureUniv]

theorem Rudin_exercise_2_24_neg :
    ¬ (∀ (X : Type*) (_ : MetricSpace X),
        (∀ A : Set X, Infinite A → ∃ x : X, x ∈ closure A) → SeparableSpace X) := by
  classical
  -- Step 1: Assume the original statement and specialize it to the discrete real line.
  intro h
  have hsepULift :
      SeparableSpace (ULift Exercise224.RealDisc) :=
        h (ULift Exercise224.RealDisc) (by infer_instance)
          (fun A hA => Exercise224.RealDisc.assumption_trivial hA)
  have hsep :
      SeparableSpace Exercise224.RealDisc :=
    separable_of_ulift hsepULift
  -- Step 2: Contradict the known non-separability of the discrete real line.
  exact RealDisc.not_separable hsep

/-
Corrected statement: the faithful translation of "every infinite subset has a limit
point" uses `AccPt` (genuine accumulation), not "lies in some closure" (which is
vacuously true for any nonempty set). With this real hypothesis, separability follows
by Rudin's argument: limit-point compactness implies total boundedness, and total
boundedness in a metric space implies separability.
-/

section Corrected

variable {X : Type*} [MetricSpace X]

/-- A totally bounded metric space is separable. -/
lemma separable_of_totallyBounded
    (hTB : TotallyBounded (Set.univ : Set X)) :
    SeparableSpace X := by
  classical
  -- Step 1: choose a finite `1/(n+1)`-net for every natural number `n`.
  choose t ht using fun n : ℕ =>
    (Metric.finite_approx_of_totallyBounded hTB) (1 / (n + 1 : ℝ)) (by
      have : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos _
      exact one_div_pos.2 this)
  refine ⟨⟨⋃ n : ℕ, t n, ?_, ?_⟩⟩
  · exact Set.countable_iUnion fun n => (ht n).2.1.countable
  · intro x
    refine Metric.mem_closure_iff.2 ?_
    intro ε εpos
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (ε := ε) εpos
    have hx := (ht n).2.2 (Set.mem_univ x)
    rcases Set.mem_iUnion.1 hx with ⟨y, hy⟩
    rcases Set.mem_iUnion.1 hy with ⟨hy', hball⟩
    refine ⟨y, Set.mem_iUnion.2 ⟨n, hy'⟩, ?_⟩
    exact lt_trans hball hn

/-- Limit-point compactness implies total boundedness in a metric space (Rudin 2.37). -/
lemma totallyBounded_of_BW
    (hBW : ∀ A : Set X, A.Infinite → ∃ p : X, AccPt p (𝓟 A)) :
    TotallyBounded (Set.univ : Set X) := by
  classical
  rw [Metric.totallyBounded_iff]
  intro ε εpos
  by_contra hntb
  push_neg at hntb
  -- Step 1: For every finite `F`, there is a point of `X` at distance `≥ ε` from all of `F`.
  have hex : ∀ (F : Set X), F.Finite → ∃ z, ∀ y ∈ F, ε ≤ dist z y := by
    intro F hF
    have hcov : ¬ (Set.univ : Set X) ⊆ ⋃ y ∈ F, Metric.ball y ε := hntb F hF
    rw [Set.not_subset] at hcov
    obtain ⟨z, _, hz⟩ := hcov
    refine ⟨z, fun y hyF => ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hz (Set.mem_iUnion₂.mpr ⟨y, hyF, Metric.mem_ball.mpr hlt⟩)
  -- Step 2: Recursively build a strictly growing chain of `ε`-separated finsets `G n`.
  let next : Finset X → Finset X := fun s =>
    insert (Classical.choose (hex (s : Set X) s.finite_toSet)) s
  let G : ℕ → Finset X := fun n => next^[n] ∅
  let z : ℕ → X := fun n => Classical.choose (hex (G n : Set X) (G n).finite_toSet)
  have hz_prop : ∀ n, ∀ y ∈ G n, ε ≤ dist (z n) y := fun n =>
    Classical.choose_spec (hex (G n : Set X) (G n).finite_toSet)
  have hG_succ : ∀ n, G (n + 1) = insert (z n) (G n) := by
    intro n
    show next^[n + 1] ∅ = insert (z n) (next^[n] ∅)
    rw [Function.iterate_succ_apply']
  have hG_mono : ∀ {m n : ℕ}, m ≤ n → G m ⊆ G n := by
    intro m n hmn
    induction n with
    | zero =>
        have : m = 0 := Nat.eq_zero_of_le_zero hmn
        subst this; exact fun _ h => h
    | succ k ih =>
        rcases Nat.lt_or_ge m (k + 1) with hlt | hge
        · have hmk : m ≤ k := Nat.lt_succ_iff.mp hlt
          intro x hx
          rw [hG_succ]
          exact Finset.mem_insert.mpr (Or.inr (ih hmk hx))
        · have : m = k + 1 := le_antisymm hmn hge
          subst this; exact fun _ h => h
  have hz_in_G : ∀ n, z n ∈ G (n + 1) := by
    intro n; rw [hG_succ]; exact Finset.mem_insert_self _ _
  -- Step 3: `z` is injective and pairwise `ε`-separated.
  have hz_pairwise : ∀ {i j : ℕ}, i < j → ε ≤ dist (z i) (z j) := by
    intro i j hij
    have hzi_in_Gj : z i ∈ G j := hG_mono hij (hz_in_G i)
    have h := hz_prop j (z i) hzi_in_Gj
    rw [dist_comm] at h
    exact h
  have hz_inj : Function.Injective z := by
    intro i j hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exfalso
      have h := hz_pairwise hlt
      rw [hij, dist_self] at h; linarith
    · exact heq
    · exfalso
      have h := hz_pairwise hgt
      rw [← hij, dist_self] at h; linarith
  -- Step 4: The range of `z` is infinite, so by `BW` it has an accumulation point.
  have hrange_inf : (Set.range z).Infinite := Set.infinite_range_of_injective hz_inj
  obtain ⟨p, hp⟩ := hBW (Set.range z) hrange_inf
  rw [accPt_iff_nhds] at hp
  -- Step 5: Extract two distinct points of `range z` inside `ball p (ε/2)`.
  obtain ⟨y₁, ⟨hy₁_ball, hy₁_range⟩, hy₁_ne⟩ :=
    hp (Metric.ball p (ε / 2)) (Metric.ball_mem_nhds p (by linarith))
  have hU2_open : IsOpen (Metric.ball p (ε / 2) \ {y₁}) := by
    rw [Set.diff_eq]
    exact Metric.isOpen_ball.inter isClosed_singleton.isOpen_compl
  have hp_in_U2 : p ∈ Metric.ball p (ε / 2) \ {y₁} :=
    ⟨Metric.mem_ball_self (by linarith),
      by simpa [Set.mem_singleton_iff] using hy₁_ne.symm⟩
  obtain ⟨y₂, ⟨⟨hy₂_ball, hy₂_ne_y₁⟩, hy₂_range⟩, _hy₂_ne⟩ :=
    hp (Metric.ball p (ε / 2) \ {y₁}) (hU2_open.mem_nhds hp_in_U2)
  -- Step 6: But two distinct elements of `range z` have distance `≥ ε` — contradiction.
  obtain ⟨i, rfl⟩ := hy₁_range
  obtain ⟨j, rfl⟩ := hy₂_range
  have hij : i ≠ j := fun h => hy₂_ne_y₁ (by simp [h])
  have hdist_ge : ε ≤ dist (z i) (z j) := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact hz_pairwise h
    · rw [dist_comm]; exact hz_pairwise h
  have h1 : dist (z i) p < ε / 2 := hy₁_ball
  have h2 : dist (z j) p < ε / 2 := hy₂_ball
  have hdist_lt : dist (z i) (z j) < ε := by
    calc dist (z i) (z j)
        ≤ dist (z i) p + dist p (z j) := dist_triangle _ _ _
      _ = dist (z i) p + dist (z j) p := by rw [dist_comm p (z j)]
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  linarith

/-- Corrected version of Rudin's exercise 2.24 (faithful to the informal statement):
a metric space in which every infinite subset has a limit point is separable. -/
theorem Rudin_exercise_2_24_corrected
    {X : Type*} [MetricSpace X]
    (hBW : ∀ A : Set X, A.Infinite → ∃ p : X, AccPt p (𝓟 A)) :
    SeparableSpace X :=
  separable_of_totallyBounded (totallyBounded_of_BW hBW)

end Corrected

end Exercise224
