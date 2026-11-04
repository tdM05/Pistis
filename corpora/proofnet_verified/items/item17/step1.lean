import Mathlib
import Pistis

open Module

/-- If `finrank F V = 1` then `V` is linearly isomorphic to `F` itself, i.e. "in fact `V = F`". -/
theorem helper_Axler_exercise_3_1_step1 {F V : Type*}
    [AddCommGroup V] [Field F] [Module F V] [FiniteDimensional F V]
    (asm1_0 : finrank F V = 1) :
    Nonempty (V ≃ₗ[F] F) := by
  refine ⟨LinearEquiv.ofFinrankEq V F ?_⟩
  rw [asm1_0, Module.finrank_self]
