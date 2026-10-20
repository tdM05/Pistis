import Mathlib
import Pistis
set_option linter.unusedTactic false

open Matrix

variable {I J : Type*} [Fintype I] [Fintype J]

/-- A real matrix *supported on* `T ⊆ I × J`: its entries outside `T` are zero (entries in `T` are
allowed to vanish). This is the paper's definition, stated in the paragraph preceding Lemma 3.2. -/
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
  -- `Matrix.single` / `Pi.single` need `DecidableEq` on the index types, which the statement does not
  -- assume. Supplied here rather than in the signature: the statement must stay exactly as frozen in
  -- `data/statement.lean`, and decidable equality on a `Fintype` is classically free anyway.
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
      (step1 : x j * y s ≠ 0) := by sorry

    -- Object introduction for segment 1.2 ("For a nonzero real $\tau$, the matrix $D_\tau$…"): the NL
    -- fixes an arbitrary nonzero τ and names the perturbed matrix. Nothing downstream uses a VALUE of
    -- τ, only `τ ≠ 0`, so an arbitrary witness keeps the remaining claims as general as the NL's.
    obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ ≠ 0 := ⟨1, one_ne_zero⟩
    set Dτ : Matrix I J ℝ := D + τ • Matrix.single s j (1 : ℝ) with hDτ
    pistis_segment "1.2"
      r"For a nonzero real $\tau$, the matrix
$D_\tau=D+\tau e_s e_j^{\mathsf T}$ is still supported on $T$,"
      (step2 : SupportedOn T Dτ) := by sorry

    pistis_segment "1.3"
      r"and
\[
 D_\tau x=\tau x_j e_s.
\]"
      (step3 : Dτ.mulVec x = (τ * x j) • (Pi.single s (1 : ℝ) : I → ℝ)) := by sorry

    pistis_segment "1.4"
      r"Thus $e_s\in\im D_\tau$."
      (step4 : (Pi.single s (1 : ℝ) : I → ℝ) ∈ LinearMap.range Dτ.mulVecLin) := by sorry

    pistis_segment "1.5"
      r"Moreover, for every $w\in\R^J$,
\[
 Dw=D_\tau w-\tau w_j e_s\in\im D_\tau,
\]"
      -- The NL displays a CHAIN, `Dw = D_τw - τw_j e_s ∈ im D_τ`: two facts that cannot be sliced into
      -- contiguous segments, so this is one segment whose assert is the whole chain (see split.json).
      (step5 : ∀ w : J → ℝ,
          (D.mulVec w = Dτ.mulVec w - (τ * w j) • (Pi.single s (1 : ℝ) : I → ℝ)) ∧
            D.mulVec w ∈ LinearMap.range Dτ.mulVecLin) := by sorry

    pistis_segment "1.6"
      r"so the entire old image $\im D$ is contained in $\im D_\tau$."
      (step6 : LinearMap.range D.mulVecLin ≤ LinearMap.range Dτ.mulVecLin) := by sorry

    -- @pistis_assumption ("$y$ annihilates $\im D$", ∀ v ∈ LinearMap.range D.mulVecLin, y ⬝ᵥ v = 0)
    -- @pistis_assumption ("$y_s\ne0$", y s ≠ 0)
    pistis_segment "1.7"
      r"On the other hand, $y$ annihilates $\im D$ and $y_s\ne0$, so
$e_s\notin\im D$."
      (step7 : (Pi.single s (1 : ℝ) : I → ℝ) ∉ LinearMap.range D.mulVecLin) := by sorry

    pistis_segment "1.8"
      r"Therefore $\rank D_\tau>\rank D$,"
      (step8 : Dτ.rank > D.rank) := by sorry

    pistis_segment "1.9"
      r"a contradiction."
      (step9 : False) := by sorry
    exact step9

  -- The reductio discharges the goal: `habsurd1` rules out `x j * y s ≠ 0`, which IS the goal.
  exact not_not.mp habsurd1
