import Mathlib
import Pistis

open Module

/-- The field `F`, as a module over itself, is spanned by `1 ∈ F`. -/
theorem helper_Axler_exercise_3_1_step2 {F : Type*} [Field F] :
    Submodule.span F {(1 : F)} = (⊤ : Submodule F F) := by
  rw [← (finrank_eq_one_iff_of_nonzero (1 : F) one_ne_zero)]
  exact Module.finrank_self F
