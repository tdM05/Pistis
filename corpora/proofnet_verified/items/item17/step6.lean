import Mathlib
import Pistis

/-- If `e` spans `V` (a one-dimensional space), every `v ∈ V` is a scalar multiple of `e`. -/
theorem helper_Axler_exercise_3_1_step6 {F V : Type*}
    [AddCommGroup V] [Field F] [Module F V] :
    ∀ (e : V), Submodule.span F {e} = (⊤ : Submodule F V) → ∀ v : V, ∃ s : F, v = s • e := by
  intro e he v
  have hv : v ∈ Submodule.span F {e} := by rw [he]; exact Submodule.mem_top
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hv
  exact ⟨s, hs.symm⟩
