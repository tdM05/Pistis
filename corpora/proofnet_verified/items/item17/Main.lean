import Mathlib
import Pistis
import items.item17.step1
import items.item17.step2
import items.item17.step3
import items.item17.step4
import items.item17.step6
import items.item17.step7
set_option linter.unusedTactic false

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators



/-Informal Statement

Show that every linear map from a one-dimensional vector space to itself is multiplication by some scalar. More precisely, prove that if $\operatorname{dim} V=1$ and $T \in \mathcal{L}(V, V)$, then there exists $a \in \mathbf{F}$ such that $T v=a v$ for all $v \in V$.
-/

theorem Axler_exercise_3_1 {F V : Type*}
  [AddCommGroup V] [Field F] [Module F V] [FiniteDimensional F V]
  (T : V →ₗ[F] V) (hT : finrank F V = 1) :
  ∃ c : F, ∀ v : V, T v = c • v:= by
  pistis_intro "17.0"
    r"Show that every linear map from a one-dimensional vector space to itself is multiplication by some scalar. More precisely, prove that if $\operatorname{dim} V=1$ and $T \in \mathcal{L}(V, V)$, then there exists $a \in \mathbf{F}$ such that $T v=a v$ for all $v \in V$."

  pistis_assumption "17.1" r"$\operatorname{dim} V=1$"
    (asm1_0 : finrank F V = 1) := by assumption
  pistis_segment "17.1"
    r"If $\operatorname{dim} V=1$, then in fact, $V=\mathbf{F}$ and"
    (step1 : Nonempty (V ≃ₗ[F] F)) := by
      exact helper_Axler_exercise_3_1_step1 asm1_0

  pistis_segment "17.2"
    r"it is spanned by $1 \in \mathbf{F}$."
    (step2 : Submodule.span F {(1 : F)} = (⊤ : Submodule F F)) := by
      exact helper_Axler_exercise_3_1_step2

  pistis_segment "17.3"
    r"Let $T$ be a linear map from $V$ to itself."
    (step3 : ∀ (a : F) (x : V), T (a • x) = a • T x) := by
      exact helper_Axler_exercise_3_1_step3 T

  pistis_segment "17.4"
    r"Let $T(1)=\lambda \in V(=\mathbf{F})$."
    (step4 : ∃ e : V, Submodule.span F {e} = (⊤ : Submodule F V) ∧ ∃ lam : V, lam = T e) := by
      exact helper_Axler_exercise_3_1_step4 T asm1_0

  pistis_wts "17.5"
    r"Step 2
2 of 3"

  pistis_segment "17.6"
    r"Every $v \in V$ is a scalar. Therefore,"
    (step6 : ∀ (e : V), Submodule.span F {e} = (⊤ : Submodule F V) → ∀ v : V, ∃ s : F, v = s • e) := by
      exact helper_Axler_exercise_3_1_step6

  pistis_segment "17.7"
    r"$$
\begin{aligned}
T(v) & =T(v \cdot 1) \\
& =v T(1) \ldots .(\text { By the linearity of } T) \\
& =v \lambda
\end{aligned}
$$"
    (step7 : ∀ (e : V) (v : V) (s : F), v = s • e → T v = s • T e) := by
      exact helper_Axler_exercise_3_1_step7 T

  pistis_conclude "17.8"
    r"Hence, $T v=\lambda v$ for every $v \in V$."

  have hgoal : ∃ c : F, ∀ v : V, T v = c • v := by
    obtain ⟨e, he, _⟩ := step4
    obtain ⟨c, hc⟩ := step6 e he (T e)
    refine ⟨c, fun v => ?_⟩
    obtain ⟨s, hs⟩ := step6 e he v
    rw [step7 e v s hs, hc, smul_smul, mul_comm, ← smul_smul, ← hs]
  exact hgoal
