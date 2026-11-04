import Mathlib
import Pistis

/-- `T` is a linear map, so it commutes with scalar multiplication. -/
theorem helper_Axler_exercise_3_1_step3 {F V : Type*}
    [AddCommGroup V] [Field F] [Module F V]
    (T : V →ₗ[F] V) :
    ∀ (a : F) (x : V), T (a • x) = a • T x := by
  intro a x
  exact T.map_smul a x
