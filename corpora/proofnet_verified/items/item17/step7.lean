import Mathlib
import Pistis

/-- By linearity of `T`, if `v = s • e` then `T v = s • T e`. -/
theorem helper_Axler_exercise_3_1_step7 {F V : Type*}
    [AddCommGroup V] [Field F] [Module F V]
    (T : V →ₗ[F] V) :
    ∀ (e : V) (v : V) (s : F), v = s • e → T v = s • T e := by
  intro e v s hv
  rw [hv, T.map_smul]
