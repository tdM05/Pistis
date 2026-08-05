import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Show that every order topology is regular.
-/

/-Informal Proof

Let $X$ be an ordered set.
First we show that $X$ is a $T_1$-space. For $x \in X$ we have that
$$
X \backslash\{x\}=\langle-\infty, x\rangle \cup\langle x,+\infty\rangle
$$
which is an open set as an union of two open intervals. Therefore, the set $\{x\}$ is closed.
Step 2
2 of 3
Now to prove that $X$ is regular we use Lemma $\mathbf{3 1 . 1 .}$
Let $x \in X$ be any point and $U \subseteq X$ any open neighborhood of $x$. Then there exist $a, b \in X$ such that $x \in\langle a, b\rangle \subseteq U$. Now we have four possibilities.
1. If there exist $x_1, x_2 \in U$ such that $a<x_1<x<x_2<b$, then
$$
x \in\left\langle x_1, x_2\right\rangle \subseteq \overline{\left\langle x_1, x_2\right\rangle} \subseteq\left[x_1, x_2\right] \subseteq\langle a, b\rangle \subseteq U
$$
2. If there exists $x_1 \in U$ such that $a<x_1<x$, but there's no $x_2 \in U$ such that $x<x_2<b$, then
$$
x \in\left\langle x_1, b\right\rangle=\left(x_1, x\right] \subseteq \overline{\left(x_1, x\right]} \subseteq\left[x_1, x\right] \subseteq\langle a, b\rangle \subseteq U
$$
3. If there exists $x_2 \in U$ such that $x<x_2<b$, but there's no $x_1 \in U$ such that $a<x_1<x$, then
$$
x \in\left\langle a, x_2\right\rangle=\left[x, x_2\right) \subseteq \overline{\left[x, x_2\right)} \subseteq\left[x, x_2\right] \subseteq\langle a, b\rangle \subseteq U
$$
4. If there's no $x_1 \in U$ such that $a<x_1<x$ and no $x_2 \in U$ such that $x<x_2<b$, then
$$
x \in\langle a, b\rangle=\{x\}=\overline{\{x\}}=\{x\} \subseteq U
$$
We have that $\overline{\{x\}}=\{x\}$ because $X$ is a $T_1$-space.
In all four cases we proved that there exists an open interval $V$ such that $x \in V \subseteq \bar{V} \subseteq U$, so $X$ is regular.
-/

theorem Munkres_exercise_31_3 {α : Type*} [PartialOrder α]
  [TopologicalSpace α] (h : OrderTopology α) : RegularSpace α := by
  sorry

/-.!
We now explain why the formal statement above is false as written.  The class
`OrderTopology α` is available for any partially ordered type, even if the
order is not linear.  When the order has incomparable elements, the order
topology may fail to be regular because the basic open rays cannot separate
points from closed sets made from incomparable elements.  The three-point poset
constructed below witnesses this phenomenon explicitly: its order topology has
only two nontrivial open sets, so the closed singleton consisting of the
incomparable point cannot be separated from the other points, and the regular
space axiom fails.
-/

namespace Exercise31_3

/-- A concrete three-point partial order: `a < b`, `c` incomparable with `a` and `b`. -/
inductive Counterexample
  | a | b | c
  deriving DecidableEq, Inhabited, Repr

open Counterexample

instance : LE Counterexample where
  le
  | a, a => True
  | a, b => True
  | b, b => True
  | c, c => True
  | _, _ => False

instance : DecidableRel ((· ≤ ·) : Counterexample → Counterexample → Prop) :=
  fun x y =>
    match x, y with
    | a, a => isTrue trivial
    | a, b => isTrue trivial
    | a, c => isFalse (by intro h; cases h)
    | b, a => isFalse (by intro h; cases h)
    | b, b => isTrue trivial
    | b, c => isFalse (by intro h; cases h)
    | c, a => isFalse (by intro h; cases h)
    | c, b => isFalse (by intro h; cases h)
    | c, c => isTrue trivial

instance : PartialOrder Counterexample where
  le := (· ≤ ·)
  le_refl := by
    intro x
    cases x <;> simp [LE.le]
  le_trans := by
    intro x y z hxy hyz
    cases x <;> cases y <;> cases z <;>
      simp [LE.le] at hxy hyz ⊢
  le_antisymm := by
    intro x y hxy hyx
    cases x with
    | a =>
        cases y with
        | a => rfl
        | b => cases hyx
        | c => cases hxy
    | b =>
        cases y with
        | a => cases hxy
        | b => rfl
        | c => cases hyx
    | c =>
        cases y with
        | a => cases hxy
        | b => cases hxy
        | c => rfl

instance : TopologicalSpace Counterexample := Preorder.topology _

instance : OrderTopology Counterexample := ⟨rfl⟩

open Set

/-- Simple facts about the strict order on the three-point poset. -/
@[simp] lemma a_lt_b : a < b := by
  constructor
  · simp [LE.le]
  · intro h; cases h

@[simp] lemma not_a_lt_a : ¬ a < a := by
  intro h; exact h.2 (by simp [LE.le])

@[simp] lemma not_a_lt_c : ¬ a < c := by
  intro h; cases h.1

@[simp] lemma not_b_lt_a : ¬ b < a := by
  intro h; cases h.1

@[simp] lemma not_b_lt_b : ¬ b < b := by
  intro h; exact h.2 (by simp [LE.le])

@[simp] lemma not_b_lt_c : ¬ b < c := by
  intro h; cases h.1

@[simp] lemma not_c_lt_a : ¬ c < a := by
  intro h; cases h.1

@[simp] lemma not_c_lt_b : ¬ c < b := by
  intro h; cases h.1

@[simp] lemma not_c_lt_c : ¬ c < c := by
  intro h; exact h.2 (by simp [LE.le])

/-- The subset consisting of the points comparable to each other. -/
def nonIso : Set Counterexample := {a, b}

@[simp] lemma mem_nonIso {x : Counterexample} : x ∈ nonIso ↔ x = a ∨ x = b := by
  classical
  simp [nonIso]

@[simp] lemma mem_nonIso_self : a ∈ nonIso := by
  classical
  simp [nonIso]

@[simp] lemma mem_nonIso_mid : b ∈ nonIso := by
  classical
  simp [nonIso]

@[simp] lemma not_mem_nonIso_iso : c ∉ nonIso := by
  classical
  simp [nonIso]

@[simp] lemma Ioi_a : Ioi a = ({b} : Set Counterexample) := by
  classical
  ext x; cases x <;> simp [Set.mem_Ioi]

@[simp] lemma Ioi_b : Ioi b = (∅ : Set Counterexample) := by
  classical
  ext x; cases x <;> simp [Set.mem_Ioi]

@[simp] lemma Ioi_c : Ioi c = (∅ : Set Counterexample) := by
  classical
  ext x; cases x <;> simp [Set.mem_Ioi]

@[simp] lemma Iio_a : Iio a = (∅ : Set Counterexample) := by
  classical
  ext x; cases x <;> simp [Set.mem_Iio]

@[simp] lemma Iio_b : Iio b = ({a} : Set Counterexample) := by
  classical
  ext x; cases x <;> simp [Set.mem_Iio]

@[simp] lemma Iio_c : Iio c = (∅ : Set Counterexample) := by
  classical
  ext x; cases x <;> simp [Set.mem_Iio]

lemma base_subset_nonIso {s : Set Counterexample}
    (hs : s ∈ {t : Set Counterexample | ∃ x, t = Ioi x ∨ t = Iio x}) :
    s ⊆ nonIso := by
  classical
  rcases hs with ⟨x, hx⟩
  rcases hx with rfl | rfl
  · cases x with
    | a =>
        intro y hy
        have : y = b := by simpa using hy
        subst this; simp [nonIso]
    | b =>
        intro y hy
        simp [Ioi_b] at hy
    | c =>
        intro y hy
        simp [Ioi_c] at hy
  · cases x with
    | a =>
        intro y hy
        simp [Iio_a] at hy
    | b =>
        intro y hy
        have : y = a := by simpa using hy
        subst this; simp [nonIso]
    | c =>
        intro y hy
        simp [Iio_c] at hy

lemma generateOpen_subset_or {s : Set Counterexample}
    (hs : TopologicalSpace.GenerateOpen
        {t : Set Counterexample | ∃ x, t = Ioi x ∨ t = Iio x} s) :
    s = (univ : Set Counterexample) ∨ s ⊆ nonIso := by
  classical
  induction hs with
  | basic t ht => exact Or.inr (base_subset_nonIso ht)
  | univ => exact Or.inl rfl
  | inter u v hu hv ihu ihv =>
      rcases ihu with hu' | hu' <;> rcases ihv with hv' | hv'
      · exact Or.inl (by simp [hu', hv'])
      · simp [hu', hv']
      · simp [hu', hv']
      · refine Or.inr ?_
        intro x hx
        exact hu' hx.1
  | sUnion T hT hInd =>
      by_cases hUniv : ∃ u ∈ T, u = (univ : Set Counterexample)
      · rcases hUniv with ⟨u, hu, rfl⟩
        refine Or.inl ?_
        have hsup : (Set.univ : Set Counterexample) ⊆ ⋃₀ T := by
          intro x hx
          have hx' : x ∈ (Set.univ : Set Counterexample) := trivial
          exact Set.mem_sUnion.mpr ⟨Set.univ, hu, hx'⟩
        have hinf : (⋃₀ T : Set Counterexample) ⊆ Set.univ := by
          intro x _; trivial
        exact Set.Subset.antisymm hinf hsup
      · have hSubset : ∀ u ∈ T, u ⊆ nonIso := by
          intro u hu
          have := hInd u hu
          rcases this with h | h
          · exact (hUniv ⟨u, hu, h⟩).elim
          · exact h
        refine Or.inr ?_
        intro x hx
        rcases Set.mem_sUnion.mp hx with ⟨u, huT, hxu⟩
        exact hSubset u huT hxu

lemma open_contains_iso {U : Set Counterexample} (hU : IsOpen U) (hc : c ∈ U) :
    U = (univ : Set Counterexample) := by
  classical
  have hGen := (isOpen_iff_generate_intervals.mp hU)
  have hoption := generateOpen_subset_or hGen
  rcases hoption with hUeq | hsubset
  · exact hUeq
  · have : False := by
        have hc' : c ∈ nonIso := hsubset hc
        simp [nonIso] at hc'
    cases this

lemma nonIso_isOpen : IsOpen (nonIso : Set Counterexample) := by
  classical
  have hopen₁ : IsOpen ({a} : Set Counterexample) := by
    simpa using (isOpen_Iio' (a := b))
  have hopen₂ : IsOpen ({b} : Set Counterexample) := by
    simpa using (isOpen_Ioi' (a := a))
  have hUnion : (nonIso : Set Counterexample) = ({a} : Set Counterexample) ∪ {b} := by
    ext x; simp [nonIso, or_comm]
  simpa [hUnion] using hopen₁.union hopen₂

lemma singleton_iso_closed : IsClosed ({c} : Set Counterexample) := by
  classical
  have hcompl : ({c} : Set Counterexample) = (nonIso : Set Counterexample)ᶜ := by
    ext x; cases x <;> simp [nonIso]
  simpa [hcompl] using nonIso_isOpen.isClosed_compl

@[simp] lemma nhds_iso_top : 𝓝 c = (⊤ : Filter Counterexample) := by
  classical
  simp [nhds_eq_order, Ioi_c, Iio_c]

@[simp] lemma nhdsSet_iso_top : 𝓝ˢ ({c} : Set Counterexample) = (⊤ : Filter Counterexample) := by
  classical
  simp [nhdsSet_singleton, nhds_iso_top]

lemma empty_not_mem_nhds_a : (∅ : Set Counterexample) ∉ 𝓝 a := by
  classical
  intro h
  rcases mem_nhds_iff.1 h with ⟨V, hVsub, hVopen, haV⟩
  have : a ∈ (∅ : Set Counterexample) := hVsub haV
  simp at this

lemma counterexample_not_regular : ¬ RegularSpace Counterexample := by
  classical
  intro h
  have hdisj :=
    (h.regular (s := ({c} : Set Counterexample)) singleton_iso_closed (by simp) :
      Disjoint (𝓝ˢ ({c} : Set Counterexample)) (𝓝 a))
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.disjoint_iff.1 hdisj
  have hUeq : U = (univ : Set Counterexample) := by
    simpa [nhdsSet_iso_top, Filter.mem_top] using hU
  have hVempty : V = (∅ : Set Counterexample) := by
    have hsubset : V ⊆ (∅ : Set Counterexample) := by
      intro x hx
      have hxU : x ∈ U := by simp [hUeq]
      exact (Set.disjoint_left.1 hUV) hxU hx
    exact Set.Subset.antisymm hsubset (Set.empty_subset _)
  simp [hVempty] at hV

end Exercise31_3

open Exercise31_3

/-.!
Corrected version: when the order is linear (so the topology has the usual rich supply of open
intervals), the expected regularity property does hold.  Mathlib already proves that a linearly
ordered type with its order topology is a `T₅` space, hence in particular a regular space; the
proof below simply cites this existing chain of instances.
-/

/-- Exhibits the concrete failing instance required to negate the original claim. -/
theorem Munkres_exercise_31_3_neg :
    ∃ (α : Type) (_ : PartialOrder α) (_ : TopologicalSpace α) (_hα : OrderTopology α),
      ¬ RegularSpace α := by
  refine ⟨Counterexample, inferInstance, inferInstance, inferInstance, counterexample_not_regular⟩

/-- Step 1: appeal to the library fact that linearly ordered order-topological spaces are `T₅`.
Step 2: every `T₅` space is automatically regular, so Lean can discharge the goal using existing
instances. -/
theorem Munkres_exercise_31_3_corrected {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] : RegularSpace α := by
  -- Step 1: infer the available `T₅` instance provided by `Mathlib.Topology.Order.T5`.
  have _ : T5Space α := inferInstance
  -- Step 2: rely on the hierarchy `T₅ ⟹ T₄ ⟹ T₃`, which makes `RegularSpace α` available.
  exact inferInstance
