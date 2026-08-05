import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

def rational (x : ℝ) := x ∈ range ((↑) : ℚ → ℝ)

/-Informal Statement

Show that the countable collection \[\{(a, b) \times (c, d) \mid a < b \text{ and } c < d, \text{ and } a, b, c, d \text{ are rational}\}\] is a basis for $\mathbb{R}^2$.
-/

/-Informal Proof

We know that $\mathcal{B}=\{(a,b)|a<b, a \text{ and } b \text rational\}$ is a basis for $\mathcal{R}$, therefore the set we are concerned with in the above question is a basis for $\mathcal{R}^2$.
-/

theorem Munkres_exercise_16_6
  (S : Set (Set (ℝ × ℝ)))
  (hS : ∀ s, s ∈ S → ∃ a b c d, (rational a ∧ rational b ∧ rational c ∧ rational d
  ∧ s = {x | ∃ x₁ x₂, x = (x₁, x₂) ∧ a < x₁ ∧ x₁ < b ∧ c < x₂ ∧ x₂ < d})) :
  IsTopologicalBasis S := by
  sorry

/-
The informal statement is false as written: any set `S` whose members happen to be rational rectangles
satisfies `hS`, even if `S` contains only one such rectangle. A singleton family can’t be a basis for
`ℝ²` because its union is not the whole space. We keep the original statement (with `sorry`) and
append the counterexample, the formal negation, and a corrected statement below.
-/

namespace Proofnet295

def rationalRectangle (a b c d : ℝ) : Set (ℝ × ℝ) :=
  {x | ∃ x₁ x₂, x = (x₁, x₂) ∧ a < x₁ ∧ x₁ < b ∧ c < x₂ ∧ x₂ < d}

lemma mem_rationalRectangle {a b c d : ℝ} {p : ℝ × ℝ} :
    p ∈ rationalRectangle a b c d ↔
      a < p.1 ∧ p.1 < b ∧ c < p.2 ∧ p.2 < d := by
  -- Step 1: prove the forward direction by unpacking the witnesses in the definition.
  constructor
  · -- Step 1.1: destruct the existential witnesses describing membership in the rectangle.
    rintro ⟨x₁, x₂, rfl, ha, hb, hc, hd⟩
    -- Step 1.2: assemble the inequalities into the desired conjunction.
    exact ⟨ha, ⟨hb, ⟨hc, hd⟩⟩⟩
  · -- Step 2: prove the reverse direction by packaging the coordinates of `p` as witnesses.
    intro h
    -- Step 2.1: provide the coordinates of `p` together with the required inequalities.
    refine ⟨p.1, p.2, ?_, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
    -- Step 2.2: the equality `p = (p.1, p.2)` is immediate by reflexivity.
    simp

lemma rationalRectangle_eq_prod (a b c d : ℝ) :
    rationalRectangle a b c d = Set.Ioo a b ×ˢ Set.Ioo c d := by
  -- Step 1: compare membership on both sides using the previous characterization.
  ext p
  -- Step 1.1: reduce equality to a pair of logical equivalences on inequalities.
  simp [mem_rationalRectangle, Set.mem_prod, Set.mem_Ioo, and_left_comm, and_assoc]

def badRect : Set (ℝ × ℝ) := rationalRectangle 0 1 0 1

def badFamily : Set (Set (ℝ × ℝ)) := {badRect}

lemma point_not_mem_badRect : (⟨(2 : ℝ), (2 : ℝ)⟩ : ℝ × ℝ) ∉ badRect := by
  -- Step 1: rewrite membership in `badRect` using the inequality-based description.
  have h02 : (0 : ℝ) < 2 := by norm_num
  have h21 : ¬ ((2 : ℝ) < 1) := by norm_num
  -- Step 1.1: simplify all inequalities to obtain `False`.
  simp [badRect, mem_rationalRectangle, h02, h21]

/-
Negation of the original statement: choose the singleton family containing `(0,1) × (0,1)`.
It satisfies the hypothesis `hS`, but the union of the family is not the whole plane, so it cannot
be a topological basis.
-/
theorem Munkres_exercise_16_6_neg :
    ¬ (∀ S : Set (Set (ℝ × ℝ)),
      (∀ s, s ∈ S →
        ∃ a b c d, (rational a ∧ rational b ∧ rational c ∧ rational d ∧
          s = {x | ∃ x₁ x₂, x = (x₁, x₂) ∧ a < x₁ ∧ x₁ < b ∧ c < x₂ ∧ x₂ < d})) →
        IsTopologicalBasis S) := by
  -- Step 1: specialize the universal quantification to the singleton family `badFamily`.
  classical
  -- Step 1.1: define the hypothesis `hS` for the witness `badFamily`.
  let S := badFamily
  have hS :
      ∀ s ∈ S,
        ∃ a b c d, (rational a ∧ rational b ∧ rational c ∧ rational d ∧
          s = {x | ∃ x₁ x₂, x = (x₁, x₂) ∧ a < x₁ ∧ x₁ < b ∧ c < x₂ ∧ x₂ < d}) := by
    -- Step 1.1.1: membership in `S` forces `s = badRect`, so provide the rational endpoints `0` and `1`.
    intro s hs
    have hs' : s = badRect := by simpa [S, badFamily]
    -- Step 1.1.2: exhibit the rational data that satisfies the requirement in `hS`.
    refine ⟨0, 1, 0, 1, ?_⟩
    -- Step 1.1.3: the four endpoints are rational, and the resulting rectangle is exactly `s`.
    have h0 : rational (0 : ℝ) := by
      refine ⟨(0 : ℚ), ?_⟩
      simp
    have h1 : rational (1 : ℝ) := by
      refine ⟨(1 : ℚ), ?_⟩
      simp
    -- Step 1.1.3.1: package the witnesses into the required conjunction.
    exact ⟨h0, ⟨h1, ⟨h0, ⟨h1, by simp [hs', badRect, rationalRectangle]⟩⟩⟩⟩
  -- Step 2: assume the conclusion holds for `S` and derive a contradiction from the missing point `(2,2)`.
  refine fun h => ?_
  -- Step 2.1: `(2,2)` cannot belong to the union of `S` (which is just `badRect`).
  have hxnot : (⟨(2 : ℝ), (2 : ℝ)⟩ : ℝ × ℝ) ∉ ⋃₀ S := by
    simpa [S, badFamily, Set.sUnion_singleton] using point_not_mem_badRect
  -- Step 2.2: the basis property would force `(2,2)` to belong to the union because `⋃₀ S = univ`.
  have hx : (⟨(2 : ℝ), (2 : ℝ)⟩ : ℝ × ℝ) ∈ ⋃₀ S := by
    have : (⟨(2 : ℝ), (2 : ℝ)⟩ : ℝ × ℝ) ∈ (Set.univ : Set (ℝ × ℝ)) := trivial
    simp [h S hS |>.sUnion_eq]
  -- Step 2.3: the incompatible memberships of `(2,2)` give the desired contradiction.
  exact hxnot hx

/-
Corrected statement:
Let `S₀` be the collection of all axis-aligned open rectangles in `ℝ²` whose endpoints are rational.
Then `S₀` forms a topological basis of `ℝ²`.
-/
def rationalIntervalFamily : Set (Set ℝ) :=
  ⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Set.Ioo (a : ℝ) b}

def rationalRectangleFamily : Set (Set (ℝ × ℝ)) :=
  Set.image2 (fun s t => s ×ˢ t) rationalIntervalFamily rationalIntervalFamily

theorem Munkres_exercise_16_6 :
    IsTopologicalBasis
      (Set.image2 (fun s t => s ×ˢ t)
        (⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Set.Ioo (a : ℝ) b})
        (⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Set.Ioo (a : ℝ) b})) := by
  -- Step 1: recall that rational open intervals form a basis for `ℝ`.
  classical
  have hℝ : IsTopologicalBasis rationalIntervalFamily := by
    -- Step 1.1: this is exactly `Real.isTopologicalBasis_Ioo_rat`.
    simpa [rationalIntervalFamily] using Real.isTopologicalBasis_Ioo_rat
  -- Step 2: the product of the one-dimensional bases yields the desired basis for `ℝ²`.
  simpa [rationalRectangleFamily] using hℝ.prod hℝ

end Proofnet295
