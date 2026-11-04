import Mathlib
import Pistis
import items.item1.step1
import items.item1.step2
import items.item1.step3
import items.item1.step4
import items.item1.step5
import items.item1.step6
import items.item1.step7
import items.item1.step8
import items.item1.step9
set_option linter.unusedTactic false

open Matrix

variable {I J : Type*} [Fintype I] [Fintype J]

def SupportedOn (T : Set (I × J)) (D : Matrix I J ℝ) : Prop :=
  ∀ s j, (s, j) ∉ T → D s j = 0

theorem kernel_support {T : Set (I × J)} {D : Matrix I J ℝ}
  (hD : SupportedOn T D)
  (hmax : ∀ A : Matrix I J ℝ, SupportedOn T A → A.rank ≤ D.rank)
  {x : J → ℝ} {y : I → ℝ}
  (hx : x ∈ LinearMap.ker D.mulVecLin)
  (hy : y ∈ LinearMap.ker Dᵀ.mulVecLin)
  {s : I} {j : J} (hsj : (s, j) ∈ T) :
  x j * y s = 0 := by
  classical
  pistis_intro "1.0"
    r"For finite index sets $I,J$, a matrix supported on
$T\subseteq I\times J$ means a real matrix whose entries outside $T$ are
zero; entries in $T$ are allowed to vanish.

\begin{lemma}[Kernels at maximum support rank]\label{lem:kernel-support}
Let $T\subseteq I\times J$, where $I$ and $J$ are finite.  Suppose that
$D:\R^J\to\R^I$ has maximum rank among all real matrices supported on $T$.
Then, for every $x\in\ker D$, every $y\in\ker D^{\mathsf T}$, and every
$(s,j)\in T$, one has $x_jy_s=0$."

  have habsurd1 : ¬(x j * y s ≠ 0) := by
    intro hsuppose1
    pistis_segment "1.1"
      r"Suppose instead that $x_jy_s\ne0$."
      (step1 : x j * y s ≠ 0) := by
        exact helper_kernel_support_step1 hsuppose1

    obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ ≠ 0 := ⟨1, one_ne_zero⟩
    set Dτ : Matrix I J ℝ := D + τ • Matrix.single s j (1 : ℝ) with hDτ
    pistis_segment "1.2"
      r"For a nonzero real $\tau$, the matrix
$D_\tau=D+\tau e_s e_j^{\mathsf T}$ is still supported on $T$,"
      (step2 : SupportedOn T Dτ) := by
        exact helper_kernel_support_step2 hDτ hD hsj

    pistis_segment "1.3"
      r"and
\[
 D_\tau x=\tau x_j e_s.
\]"
      (step3 : Dτ.mulVec x = (τ * x j) • (Pi.single s (1 : ℝ) : I → ℝ)) := by
        exact helper_kernel_support_step3 hDτ (by simpa using LinearMap.mem_ker.mp hx)

    pistis_segment "1.4"
      r"Thus $e_s\in\im D_\tau$."
      (step4 : (Pi.single s (1 : ℝ) : I → ℝ) ∈ LinearMap.range Dτ.mulVecLin) := by
        exact helper_kernel_support_step4 hτ step3 hsuppose1

    pistis_segment "1.5"
      r"Moreover, for every $w\in\R^J$,
\[
 Dw=D_\tau w-\tau w_j e_s\in\im D_\tau,
\]"

      (step5 : ∀ w : J → ℝ,
          (D.mulVec w = Dτ.mulVec w - (τ * w j) • (Pi.single s (1 : ℝ) : I → ℝ)) ∧
            D.mulVec w ∈ LinearMap.range Dτ.mulVecLin) := by
        exact helper_kernel_support_step5 hDτ step4

    pistis_segment "1.6"
      r"so the entire old image $\im D$ is contained in $\im D_\tau$."
      (step6 : LinearMap.range D.mulVecLin ≤ LinearMap.range Dτ.mulVecLin) := by
        exact helper_kernel_support_step6 step5

    pistis_assumption "1.7" r"$y$ annihilates $\im D$"
      (hyann : ∀ v ∈ LinearMap.range D.mulVecLin, y ⬝ᵥ v = 0) := by
        rintro v ⟨w, rfl⟩
        have hy' : Dᵀ.mulVec y = 0 := LinearMap.mem_ker.mp hy
        have key := Matrix.dotProduct_transpose_mulVec D w y
        rw [hy', dotProduct_zero] at key
        exact key.symm
    pistis_assumption "1.7" r"$y_s\ne0$"
      (hys : y s ≠ 0) := by
        intro h
        exact hsuppose1 (by rw [h, mul_zero])
    pistis_segment "1.7"
      r"On the other hand, $y$ annihilates $\im D$ and $y_s\ne0$, so
$e_s\notin\im D$."
      (step7 : (Pi.single s (1 : ℝ) : I → ℝ) ∉ LinearMap.range D.mulVecLin) := by
        exact helper_kernel_support_step7 hyann hys

    pistis_segment "1.8"
      r"Therefore $\rank D_\tau>\rank D$,"
      (step8 : Dτ.rank > D.rank) := by
        exact helper_kernel_support_step8 step4 step6 step7

    pistis_segment "1.9"
      r"a contradiction."
      (step9 : False) := by
        exact helper_kernel_support_step9 hmax step2 step8
    exact step9

  exact not_not.mp habsurd1
