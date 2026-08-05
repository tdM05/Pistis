import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀ s, (∀ t ∈ s, t ∈ T) → sUnion s ∈ T)

/-Informal Statement

If $\mathcal{T}_\alpha$ is a family of topologies on $X$, show that $\bigcup \mathcal{T}_\alpha$ does not need to be a topology on $X$.
-/

/-Informal Proof

On the other hand, the union $\bigcup_\alpha \mathcal{T}_\alpha$ is in general not a topology on $X$. For instance, let $X=\{a, b, c\}$. Then $\mathcal{T}_1=\{\emptyset, X,\{a\}\}$ and $\mathcal{T}_2=\{\emptyset, X,\{b\}\}$ are topologies on $X$ but $\mathcal{T}_1 \cup \mathcal{T}_2=$ $\{\emptyset, X,\{a\},\{b\}\}$ is not.
-/

/-
============================================================================
PROOF STRATEGY:
============================================================================
We construct a counterexample using X = Fin 3 = {0, 1, 2} and I = Bool.

Step 1: Define X = Fin 3 (a 3-element set)
Step 2: Define I = Bool (index set with two elements)
Step 3: Define two topologies:
  - T(false) = {∅, X, {0}}     (the trivial topology augmented with {0})
  - T(true)  = {∅, X, {1}}     (the trivial topology augmented with {1})

Step 4: Verify each T(i) is a topology
  - Contains univ ✓
  - Closed under finite intersections ✓
  - Closed under arbitrary unions ✓

Step 5: Show T(false) ∪ T(true) = {∅, X, {0}, {1}} is NOT a topology
  - The union {0} ∪ {1} = {0, 1} should be in the topology
  - But {0, 1} ∉ {∅, X, {0}, {1}}

============================================================================
-/

-- Step 1: Define the family of topologies T
-- T(false) = {∅, univ, {0}}
-- T(true)  = {∅, univ, {1}}
private def my_T : Bool → Set (Set (Fin 3)) := fun b =>
  if b then {∅, Set.univ, {1}} else {∅, Set.univ, {0}}

-- Step 4.1: Helper lemma - each T(i) contains univ
private lemma my_T_has_univ (i : Bool) : Set.univ ∈ my_T i := by
  unfold my_T
  cases i <;> simp [Set.mem_insert_iff]

-- Step 4.2: Helper lemma - each T(i) is closed under binary intersection
private lemma my_T_inter_closed (i : Bool) (s t : Set (Fin 3)) (hs : s ∈ my_T i) (ht : t ∈ my_T i) :
    s ∩ t ∈ my_T i := by
  unfold my_T at hs ht ⊢
  cases i
  -- Case i = false: T(false) = {∅, univ, {0}}
  · simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht ⊢
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
      simp only [Set.inter_self, Set.univ_inter, Set.inter_univ, Set.inter_empty,
        Set.empty_inter, true_or, or_true]
  -- Case i = true: T(true) = {∅, univ, {1}}
  · simp only [↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht ⊢
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
      simp only [Set.inter_self, Set.univ_inter, Set.inter_univ, Set.inter_empty,
        Set.empty_inter, true_or, or_true]

-- Step 4.3: Helper lemma - each T(i) is closed under arbitrary unions
private lemma my_T_sUnion_closed (i : Bool) (S : Set (Set (Fin 3))) (hS : ∀ t ∈ S, t ∈ my_T i) :
    ⋃₀ S ∈ my_T i := by
  unfold my_T at hS ⊢
  cases i
  -- Case i = false: T(false) = {∅, univ, {0}}
  · simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff] at hS ⊢
    by_cases huniv : Set.univ ∈ S
    · -- If univ ∈ S, then ⋃₀ S = univ
      right; left
      ext x
      simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
      exact ⟨Set.univ, huniv, Set.mem_univ x⟩
    · by_cases h0 : ({0} : Set (Fin 3)) ∈ S
      · -- If {0} ∈ S but univ ∉ S, then ⋃₀ S = {0}
        right; right
        ext x
        simp only [Set.mem_sUnion, Set.mem_singleton_iff]
        constructor
        · intro ⟨t, htS, hxt⟩
          have ht_mem := hS t htS
          rcases ht_mem with rfl | rfl | rfl
          · exact (Set.notMem_empty x hxt).elim
          · exact (huniv htS).elim
          · exact hxt
        · intro hx
          exact ⟨{0}, h0, hx⟩
      · -- If neither univ nor {0} is in S, then S ⊆ {∅}
        left
        ext x
        constructor
        · intro ⟨t, htS, hxt⟩
          have ht_mem := hS t htS
          rcases ht_mem with rfl | rfl | rfl
          · exact hxt
          · exact (huniv htS).elim
          · exact (h0 htS).elim
        · intro h
          exact h.elim

  -- Case i = true: T(true) = {∅, univ, {1}}
  · simp only [↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff] at hS ⊢
    by_cases huniv : Set.univ ∈ S
    · -- If univ ∈ S, then ⋃₀ S = univ
      right; left
      ext x
      simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
      exact ⟨Set.univ, huniv, Set.mem_univ x⟩
    · by_cases h1 : ({1} : Set (Fin 3)) ∈ S
      · -- If {1} ∈ S but univ ∉ S
        -- All elements are either ∅ or {1}, so ⋃₀ S = {1}
        right; right
        ext x
        simp only [Set.mem_sUnion, Set.mem_singleton_iff]
        constructor
        · intro ⟨t, htS, hxt⟩
          have ht_mem := hS t htS
          rcases ht_mem with rfl | rfl | rfl
          · exact (Set.notMem_empty x hxt).elim
          · exact (huniv htS).elim
          · exact hxt
        · intro hx
          exact ⟨{1}, h1, hx⟩
      · -- If neither univ nor {1} is in S, then S ⊆ {∅}
        left
        ext x
        constructor
        · intro ⟨t, htS, hxt⟩
          have ht_mem := hS t htS
          rcases ht_mem with rfl | rfl | rfl
          · exact hxt
          · exact (huniv htS).elim
          · exact (h1 htS).elim
        · intro h
          exact h.elim

-- Step 4: Each T(i) is a topology
private lemma my_T_is_topology (i : Bool) : is_topology (Fin 3) (my_T i) :=
  ⟨my_T_has_univ i, my_T_inter_closed i, my_T_sUnion_closed i⟩

-- Step 5: The union ⋃ i, T(i) is NOT a topology
private lemma my_T_union_not_topology : ¬ is_topology (Fin 3) (⋃ i : Bool, my_T i) := by
  intro h_is_top
  unfold is_topology at h_is_top
  obtain ⟨_, _, h_union⟩ := h_is_top

  -- Step 5.1: Note that {0} ∈ ⋃ i, T i (from T(false))
  -- Step 5.2: Note that {1} ∈ ⋃ i, T i (from T(true))
  -- Step 5.3: By the sUnion axiom, ⋃₀ {{0}, {1}} = {0, 1} should be in the union
  -- Step 5.4: But {0, 1} ∉ {∅, univ, {0}, {1}}

  -- Define S = {{0}, {1}}
  let S : Set (Set (Fin 3)) := {{0}, {1}}

  -- Step 5.1-5.2: Show that all elements of S are in ⋃ i, T i
  have hS : ∀ t ∈ S, t ∈ ⋃ i : Bool, my_T i := by
    intro t ht
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · -- {0} ∈ T(false)
      simp only [Set.mem_iUnion, my_T]
      use false
      simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
    · -- {1} ∈ T(true)
      simp only [Set.mem_iUnion, my_T]
      use true
      simp only [↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]

  -- Step 5.3: Apply the union axiom to get that ⋃₀ S ∈ ⋃ i, T i
  have h_sUnion_in : ⋃₀ S ∈ ⋃ i : Bool, my_T i := h_union S hS

  -- Step 5.4: Compute ⋃₀ S = {0, 1}
  have h_sUnion_eq : ⋃₀ S = ({0, 1} : Set (Fin 3)) := by
    ext x
    simp only [S, Set.mem_sUnion, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨t, ht, hxt⟩
      rcases ht with rfl | rfl
      · left; exact hxt
      · right; exact hxt
    · intro hx
      rcases hx with hx | hx
      · exact ⟨{0}, Or.inl rfl, hx⟩
      · exact ⟨{1}, Or.inr rfl, hx⟩

  -- Step 5.5: Show that {0, 1} ∉ ⋃ i, T i
  -- The union is {∅, univ, {0}} ∪ {∅, univ, {1}} = {∅, univ, {0}, {1}}
  rw [h_sUnion_eq] at h_sUnion_in

  -- {0, 1} is in some T(i), so either in T(false) or T(true)
  simp only [Set.mem_iUnion, my_T] at h_sUnion_in
  obtain ⟨i, hi⟩ := h_sUnion_in

  -- Step 5.6: Case analysis on i to derive contradiction
  -- Both cases lead to contradiction because {0,1} is not in either T(false) or T(true)
  cases i
  -- Case i = false: {0, 1} ∈ T(false) = {∅, univ, {0}}
  · simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with h_eq | h_eq | h_eq
    · -- {0, 1} = ∅ is false
      have h0_in : (0 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
      rw [h_eq] at h0_in
      exact h0_in
    · -- {0, 1} = univ is false (univ has 3 elements)
      have h2_not_in : (2 : Fin 3) ∉ ({0, 1} : Set (Fin 3)) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.reduceEq, or_self, not_false_eq_true]
      rw [h_eq] at h2_not_in
      exact h2_not_in (Set.mem_univ 2)
    · -- {0, 1} = {0} is false
      have h1_in : (1 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
      rw [h_eq] at h1_in
      simp only [Set.mem_singleton_iff, Fin.reduceEq] at h1_in
  -- Case i = true: {0, 1} ∈ T(true) = {∅, univ, {1}}
  · simp only [↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with h_eq | h_eq | h_eq
    · -- {0, 1} = ∅ is false
      have h0_in : (0 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
      rw [h_eq] at h0_in
      exact h0_in
    · -- {0, 1} = univ is false
      have h2_not_in : (2 : Fin 3) ∉ ({0, 1} : Set (Fin 3)) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.reduceEq, or_self, not_false_eq_true]
      rw [h_eq] at h2_not_in
      exact h2_not_in (Set.mem_univ 2)
    · -- {0, 1} = {1} is false
      have h0_in : (0 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
      rw [h_eq] at h0_in
      simp only [Set.mem_singleton_iff, Fin.reduceEq] at h0_in

-- Universe-polymorphic version using ULift
-- We lift Fin 3 and Bool to arbitrary universes
universe u v

private def my_T_lifted : ULift.{v} Bool → Set (Set (ULift.{u} (Fin 3))) := fun ⟨b⟩ =>
  if b then {∅, Set.univ, {⟨1⟩}} else {∅, Set.univ, {⟨0⟩}}

private lemma my_T_lifted_is_topology (i : ULift.{v} Bool) :
    is_topology (ULift.{u} (Fin 3)) (my_T_lifted i) := by
  obtain ⟨i⟩ := i
  unfold is_topology my_T_lifted
  constructor
  -- univ ∈ T(i)
  · cases i <;> simp [Set.mem_insert_iff]
  constructor
  -- intersection closure
  · intro s t hs ht
    cases i
    · simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht ⊢
      rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
        simp only [Set.inter_self, Set.univ_inter, Set.inter_univ, Set.inter_empty,
          Set.empty_inter, true_or, or_true]
    · simp only [↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht ⊢
      rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
        simp only [Set.inter_self, Set.univ_inter, Set.inter_univ, Set.inter_empty,
          Set.empty_inter, true_or, or_true]
  -- sUnion closure
  · intro S hS
    cases i
    -- Case i = false: T(false) = {∅, univ, {⟨0⟩}}
    · simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff] at hS ⊢
      by_cases huniv : Set.univ ∈ S
      · right; left
        ext x
        simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
        exact ⟨Set.univ, huniv, Set.mem_univ x⟩
      · by_cases h0 : ({⟨0⟩} : Set (ULift (Fin 3))) ∈ S
        · right; right
          ext x
          simp only [Set.mem_sUnion, Set.mem_singleton_iff]
          constructor
          · intro ⟨t, htS, hxt⟩
            have ht_mem := hS t htS
            rcases ht_mem with rfl | rfl | rfl
            · exact (Set.notMem_empty x hxt).elim
            · exact (huniv htS).elim
            · exact hxt
          · intro hx
            exact ⟨{⟨0⟩}, h0, hx⟩
        · left
          ext x
          constructor
          · intro ⟨t, htS, hxt⟩
            have ht_mem := hS t htS
            rcases ht_mem with rfl | rfl | rfl
            · exact hxt
            · exact (huniv htS).elim
            · exact (h0 htS).elim
          · intro h
            exact h.elim
    -- Case i = true: T(true) = {∅, univ, {⟨1⟩}}
    · simp only [↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff] at hS ⊢
      by_cases huniv : Set.univ ∈ S
      · right; left
        ext x
        simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
        exact ⟨Set.univ, huniv, Set.mem_univ x⟩
      · by_cases h1 : ({⟨1⟩} : Set (ULift (Fin 3))) ∈ S
        · right; right
          ext x
          simp only [Set.mem_sUnion, Set.mem_singleton_iff]
          constructor
          · intro ⟨t, htS, hxt⟩
            have ht_mem := hS t htS
            rcases ht_mem with rfl | rfl | rfl
            · exact (Set.notMem_empty x hxt).elim
            · exact (huniv htS).elim
            · exact hxt
          · intro hx
            exact ⟨{⟨1⟩}, h1, hx⟩
        · left
          ext x
          constructor
          · intro ⟨t, htS, hxt⟩
            have ht_mem := hS t htS
            rcases ht_mem with rfl | rfl | rfl
            · exact hxt
            · exact (huniv htS).elim
            · exact (h1 htS).elim
          · intro h
            exact h.elim

private lemma my_T_lifted_union_not_topology :
    ¬ is_topology (ULift.{u} (Fin 3)) (⋃ i : ULift.{v} Bool, my_T_lifted i) := by
  intro h_is_top
  unfold is_topology at h_is_top
  obtain ⟨_, _, h_union⟩ := h_is_top

  let S : Set (Set (ULift (Fin 3))) := {{⟨0⟩}, {⟨1⟩}}

  have hS : ∀ t ∈ S, t ∈ ⋃ i : ULift Bool, my_T_lifted i := by
    intro t ht
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · simp only [Set.mem_iUnion, my_T_lifted]
      use ⟨false⟩
      simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
    · simp only [Set.mem_iUnion, my_T_lifted]
      use ⟨true⟩
      simp only [↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]

  have h_sUnion_in : ⋃₀ S ∈ ⋃ i : ULift Bool, my_T_lifted i := h_union S hS

  have h_sUnion_eq : ⋃₀ S = ({⟨0⟩, ⟨1⟩} : Set (ULift (Fin 3))) := by
    ext x
    simp only [S, Set.mem_sUnion, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨t, ht, hxt⟩
      rcases ht with rfl | rfl
      · left; exact hxt
      · right; exact hxt
    · intro hx
      rcases hx with hx | hx
      · exact ⟨{⟨0⟩}, Or.inl rfl, hx⟩
      · exact ⟨{⟨1⟩}, Or.inr rfl, hx⟩

  rw [h_sUnion_eq] at h_sUnion_in

  simp only [Set.mem_iUnion, my_T_lifted] at h_sUnion_in
  obtain ⟨⟨i⟩, hi⟩ := h_sUnion_in

  cases i
  · simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with h_eq | h_eq | h_eq
    · have h0_in : (⟨0⟩ : ULift (Fin 3)) ∈ ({⟨0⟩, ⟨1⟩} : Set (ULift (Fin 3))) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
      rw [h_eq] at h0_in
      exact h0_in
    · have h2_not_in : (⟨2⟩ : ULift (Fin 3)) ∉ ({⟨0⟩, ⟨1⟩} : Set (ULift (Fin 3))) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, ULift.ext_iff, Fin.reduceEq, or_self,
          not_false_eq_true]
      rw [h_eq] at h2_not_in
      exact h2_not_in (Set.mem_univ (⟨2⟩ : ULift (Fin 3)))
    · have h1_in : (⟨1⟩ : ULift (Fin 3)) ∈ ({⟨0⟩, ⟨1⟩} : Set (ULift (Fin 3))) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
      rw [h_eq] at h1_in
      simp only [Set.mem_singleton_iff, ULift.ext_iff, Fin.reduceEq] at h1_in
  · simp only [↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with h_eq | h_eq | h_eq
    · have h0_in : (⟨0⟩ : ULift (Fin 3)) ∈ ({⟨0⟩, ⟨1⟩} : Set (ULift (Fin 3))) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
      rw [h_eq] at h0_in
      exact h0_in
    · have h2_not_in : (⟨2⟩ : ULift (Fin 3)) ∉ ({⟨0⟩, ⟨1⟩} : Set (ULift (Fin 3))) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, ULift.ext_iff, Fin.reduceEq, or_self,
          not_false_eq_true]
      rw [h_eq] at h2_not_in
      exact h2_not_in (Set.mem_univ (⟨2⟩ : ULift (Fin 3)))
    · have h0_in : (⟨0⟩ : ULift (Fin 3)) ∈ ({⟨0⟩, ⟨1⟩} : Set (ULift (Fin 3))) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
      rw [h_eq] at h0_in
      simp only [Set.mem_singleton_iff, ULift.ext_iff, Fin.reduceEq] at h0_in

theorem Munkres_exercise_13_4a2 :
  ∃ (X I : Type*) (T : I → Set (Set X)),
  (∀ i, is_topology X (T i)) ∧ ¬  is_topology X (⋃ i : I, T i) :=
  ⟨ULift (Fin 3), ULift Bool, my_T_lifted, my_T_lifted_is_topology, my_T_lifted_union_not_topology⟩
