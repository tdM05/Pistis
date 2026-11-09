import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Basic.Real.Basic

section Current
variable {I J : Type*} [Fintype I] [Fintype J]

def SupportedOnCurrent (T : Set (I × J)) (D : Matrix I J ℝ) : Prop :=
  ∀ s j, (s, j) ∉ T → D s j = 0
end Current

section Faithful
def SupportedOnFaithful {I J : Type*} [Fintype I] [Fintype J] (T : Set (I × J)) (D : Matrix I J ℝ) : Prop :=
  ∀ s j, (s, j) ∉ T → D s j = 0
end Faithful


-- application works (when it should not since NL enforces finite) on current version
example (T : Set (ℕ × ℕ)) (D : Matrix ℕ ℕ ℝ) : Prop := SupportedOnCurrent T D

-- this is what it should be
example (T : Set (ℕ × ℕ)) (D : Matrix ℕ ℕ ℝ) : Prop := SupportedOnFaithful T D
