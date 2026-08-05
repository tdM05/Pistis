import Mathlib

open Filter Set TopologicalSpace Topology
open scoped Topology



/-Informal Statement

Show that if $Y$ is a subspace of $X$, and $A$ is a subset of $Y$, then the topology $A$ inherits as a subspace of $Y$ is the same as the topology it inherits as a subspace of $X$.
-/

/-Informal Proof

Exercise 16.1. Let $\mathcal{T}$ be the topology $A$ inherits as a subspace of $Y$, and $\mathcal{O}$ be the topology it inherits as a subspace of $X$. A (standard) basis element for $\mathcal{T}$ has the form $U \cap A$ where $U$ is open in $Y$, so is of the form $(Y \cap V) \cap A=V \cap A$ where $V$ is open in $X$. Therefore every basis element for $\mathcal{T}$ is also a basis element for $\mathcal{O}$. Conversely, a (standard) basis element for $\mathcal{O}$ have the form $W \cap A=W \cap Y \cap A$ where $W$ is open in $X$. Since $W \cap Y$ is open in $Y$, this is a basis element for $\mathcal{T}$, so every basis element for $\mathcal{O}$ is a basis element for $\mathcal{T}$. It follows that $\mathcal{T}=\mathcal{O}$.
-/

theorem Munkres_exercise_16_1 {X : Type*} [TopologicalSpace X]
  (Y : Set X)
  (A : Set Y) :
  ∀ U : Set A, IsOpen U ↔ IsOpen (Subtype.val '' U) := by
  sorry

/-
Why the formalized statement is false.
The Lean goal says that for *every* ambient space `X`, every subspace `Y ⊆ X`,
every subset `A ⊆ Y`, and every open set `U` of the subspace `A`, the image
`Subtype.val '' U` must be open inside `Y`.  However, if we pick a universe-lifted
copy of the real line `ULift ℝ` for `X`, let `Y = ULift ℝ`, and let `A` be the closed
ray `{x : ℝ | x ≤ 0}`, then the entire space `U = Set.univ` is open in the subspace
topology on `A` while its image is exactly `{x : ℝ | x ≤ 0}`, a set that is not open
in `ULift ℝ` (hence not open when viewed downstairs in `ℝ` either).
Therefore the claimed equivalence fails in that concrete situation.
-/


abbrev BadX := ULift ℝ
abbrev badY : Set BadX := Set.univ
abbrev badA : Set badY := fun y : badY => (((y : BadX).down : ℝ) ≤ 0)
abbrev badU : Set badA := Set.univ

-- Homeomorphism witnessing that `badY = Set.univ` is just `BadX`.
def badYHomeoBadX : badY ≃ₜ BadX :=
{ toEquiv :=
  { toFun := fun y => y
    invFun := fun x => ⟨x, trivial⟩
    left_inv := by
      intro y
      cases y with
      | mk val property =>
          cases property
          rfl
    right_inv := by intro x; rfl }
  continuous_toFun := by continuity
  continuous_invFun := by continuity }

-- Compose with the standard `ulift` homeomorphism to identify `badY` with `ℝ`.
def badYHomeoReal : badY ≃ₜ ℝ :=
  badYHomeoBadX.trans Homeomorph.ulift

@[simp]
lemma mem_badA (y : badY) : y ∈ badA ↔ ((y : BadX).down : ℝ) ≤ 0 :=
  Iff.rfl

@[simp]
lemma mem_badU (u : badA) : u ∈ badU :=
  by
    -- Step 1: `badU` is syntactically `Set.univ`, so every element belongs to it.
    simp [badU]

lemma badU_isOpen : IsOpen badU := by
  -- Step 1: `badU` equals `Set.univ`, so we reduce to the standard fact that `Set.univ` is open.
  -- Step 2: Apply the `IsOpen.univ` lemma and rewrite back in terms of `badU`.
  simp [badU]

lemma badU_image :
    Subtype.val '' badU = badA := by
  -- Step 1: Show equality of sets by extensionality.
  ext y
  constructor
  · -- Step 1.1: If `y` lies in the image, it comes from some `u : badA`.
    intro hy
    rcases hy with ⟨u, -, rfl⟩
    -- Step 1.2: Membership follows from `u.property`, i.e. the fact that `u ∈ badA`.
    exact u.property
  · -- Step 2.1: Start with an arbitrary `y` in `badA`.
    intro hy
    -- Step 2.2: Exhibit `⟨y, hy⟩ : badA` whose image is exactly `y`.
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    -- Step 2.3: Use that `badU = Set.univ` to discharge the membership goal.
    simp [badU]

lemma badA_not_isOpen : ¬ IsOpen badA := by
  -- Step 1: Argue by contradiction and assume `badA` were open.
  intro hOpen
  -- Step 2: Transport openness along the homeomorphism to a statement about `{x | x ≤ 0} ⊆ ℝ`.
  let e := badYHomeoReal
  have hOpen_real : IsOpen {x : ℝ | x ≤ 0} := by
    -- Openness is preserved under preimage of a homeomorphism.
    have h_preimage : e.symm ⁻¹' badA = {x : ℝ | x ≤ 0} := by
      ext x
      constructor <;> intro hx <;> simpa [e, badYHomeoReal, badYHomeoBadX, badA, badY]
        using hx
    have h_preimage_open : IsOpen (e.symm ⁻¹' badA) :=
      hOpen.preimage e.symm.continuous
    simpa [h_preimage] using h_preimage_open
  -- Step 3: But `{x | x ≤ 0}` is not open in `ℝ` (its interior is `{x | x < 0}`).
  have hInt : interior ({x : ℝ | x ≤ 0}) = {x : ℝ | x < 0} := by
    simpa [Set.Iic, Set.Iio] using (interior_Iic (a := (0 : ℝ)))
  have hHalfline_not_open : ¬ IsOpen ({x : ℝ | x ≤ 0} : Set ℝ) := by
    intro h
    have hInt_eq : interior ({x : ℝ | x ≤ 0}) = ({x : ℝ | x ≤ 0}) :=
      interior_eq_iff_isOpen.mpr h
    have h0_mem : (0 : ℝ) ∈ interior ({x : ℝ | x ≤ 0}) := by
      simp [hInt_eq]
    have h0_not_mem : (0 : ℝ) ∉ interior ({x : ℝ | x ≤ 0}) := by
      simp [hInt]
    exact h0_not_mem h0_mem
  exact hHalfline_not_open hOpen_real

lemma badU_image_not_isOpen : ¬ IsOpen (Subtype.val '' badU) := by
  -- Step 1: Substitute the explicit description of the image.
  -- Step 2: Apply the previous lemma.
  intro hOpen
  -- Step 2.1: Translate the openness of the image to openness of `badA`.
  have : IsOpen badA := by
    -- avoid `simp` triggers by an explicit rewrite.
    convert hOpen using 1
    · exact badU_image.symm
  -- Step 2.2: Contradict the previously established non-openness.
  exact badA_not_isOpen this

lemma counterexample_data :
    ∃ (X : Type*) (_instX : TopologicalSpace X) (Y : Set X) (A : Set Y) (U : Set A),
      IsOpen U ∧ ¬ IsOpen (Subtype.val '' U) :=
  ⟨BadX, inferInstance, badY, badA, badU, badU_isOpen, badU_image_not_isOpen⟩

/- The negation of the original (incorrect) statement. -/
theorem Munkres_exercise_16_1_neg :
    ¬ (∀ (X : Type*) [TopologicalSpace X] (Y : Set X) (A : Set Y),
      ∀ U : Set A, IsOpen U ↔ IsOpen (Subtype.val '' U)) := by
  -- Step 1: Work classically for convenience when choosing elements.
  classical
  -- Step 2: Assume the false universal statement holds.
  intro h
  -- Step 3: Extract the concrete counterexample data.
  obtain ⟨X, instX, Y, A, U, hU_open, hU_image_closed⟩ := counterexample_data
  -- Step 4: Apply the (incorrect) universal hypothesis to this specific data.
  have h_equiv : IsOpen U ↔ IsOpen (Subtype.val '' U) := @h X instX Y A U
  -- Step 4.1: Use the forward implication provided by the equivalence.
  have h_image_open : IsOpen (Subtype.val '' U) := (h_equiv.mp hU_open)
  -- Step 5: Contradict the openness of the image using the witness.
  exact hU_image_closed h_image_open

/-
Corrected version (with proof).
Correct statement: the inclusion map `(fun a : A => (a : X))` is *inducing*,
so the topology on `A` is exactly the one induced from `X`.  This captures
precisely the idea that taking subspaces in two steps (first inside `Y`, then
inside `X`) is the same as inducing the topology from `X` directly.
-/
theorem Munkres_exercise_16_1_corrected {X : Type*} [TopologicalSpace X]
    (Y : Set X) (A : Set Y) :
    IsInducing (fun a : A => (a : X)) := by
  -- Step 1: By definition, `Inducing` asks us to identify the topology on `A`
  --         with the topology induced from `X` through the composite inclusion.
  refine ⟨?_⟩
  -- Step 2: Expand both topologies using `Subtype.instTopologicalSpaceSubtype`
  --         and combine them with `induced_compose`.
  -- Step 3: Observe that the composite `Subtype.val ∘ Subtype.val`
  --         is the function `fun a : A => (a : X)`.
  change
      TopologicalSpace.induced (Subtype.val : A → Y)
          (TopologicalSpace.induced (Subtype.val : Y → X) inferInstance)
        =
        TopologicalSpace.induced (fun a : A => (a : X)) inferInstance
  simpa [Function.comp] using
    (induced_compose
      (tγ := inferInstance)
      (f := (Subtype.val : A → Y))
      (g := (Subtype.val : Y → X)))
