import Mathlib
import Pistis

open Module

/-- There is a generator `e` of the one-dimensional space `V` (it spans `V`), and we may name
`λ := T e`. -/
theorem helper_Axler_exercise_3_1_step4 {F V : Type*}
    [AddCommGroup V] [Field F] [Module F V] [FiniteDimensional F V]
    (T : V →ₗ[F] V) (asm1_0 : finrank F V = 1) :
    ∃ e : V, Submodule.span F {e} = (⊤ : Submodule F V) ∧ ∃ lam : V, lam = T e := by
  obtain ⟨e, he, _⟩ := (finrank_eq_one_iff' (K := F) (V := V)).mp asm1_0
  refine ⟨e, ?_, T e, rfl⟩
  exact (finrank_eq_one_iff_of_nonzero e he).mp asm1_0
