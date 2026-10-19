/-
`items/item1/Main.lean` says the same thing with `pistis_intro` / `pistis_segment`. This file says it
with nothing but Lean: the proof a Lean user would write, cut into regions by `--|` markers.

A `--| <loc>` line opens a region; the region runs to the line before the next marker (or to the end
of the file), trimmed to its first and last non-whitespace character. The markers are COMMENTS, so
they carry no meaning for Lean and none for the alignment either: they are a *seed* for the top-level
`S_F` spans, in the same way `split.json`'s `assert` seeds an `S_N` span. The spans on disk are
UTF-16 offsets into this file verbatim; re-cut them in the UI and the markers stop being the truth.

Nothing is asserted twice. A region's text is the whole of its formal side — there is no separate
"formal context" to read it against, because `D + τ • Matrix.single s j 1` is IN region 1.2, where
the prose that defines `D_τ` can be linked straight to it. See `kpistis/README.md`, *No formal
context*.
-/
--| hdr
import Mathlib
open Matrix
set_option linter.unusedVariables false

--| idx
variable {I J : Type*} [Fintype I] [Fintype J]

--| def
def SupportedOn (T : Set (I × J)) (D : Matrix I J ℝ) : Prop :=
  ∀ s j, (s, j) ∉ T → D s j = 0

--| thm
theorem kernel_support {T : Set (I × J)} {D : Matrix I J ℝ}
    (hD : SupportedOn T D)
    (hmax : ∀ A : Matrix I J ℝ, SupportedOn T A → A.rank ≤ D.rank)
    {x : J → ℝ} {y : I → ℝ}
    (hx : x ∈ LinearMap.ker D.mulVecLin)
    (hy : y ∈ LinearMap.ker Dᵀ.mulVecLin)
    {s : I} {j : J} (hsj : (s, j) ∈ T) :
    x j * y s = 0 := by
--| tech
  classical
--| 1.1
  refine not_not.mp fun hne : x j * y s ≠ 0 => ?_
--| 1.2
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ ≠ 0 := ⟨1, one_ne_zero⟩
  set Dτ : Matrix I J ℝ := D + τ • Matrix.single s j (1 : ℝ) with hDτ
  have hsupp : SupportedOn T Dτ := by sorry
--| 1.3
  have hDτx : Dτ.mulVec x = (τ * x j) • (Pi.single s (1 : ℝ) : I → ℝ) := by sorry
--| 1.4
  have hes : (Pi.single s (1 : ℝ) : I → ℝ) ∈ LinearMap.range Dτ.mulVecLin := by sorry
--| 1.5
  have hDw : ∀ w : J → ℝ,
      D.mulVec w = Dτ.mulVec w - (τ * w j) • (Pi.single s (1 : ℝ) : I → ℝ) ∧
        D.mulVec w ∈ LinearMap.range Dτ.mulVecLin := by sorry
--| 1.6
  have himg : LinearMap.range D.mulVecLin ≤ LinearMap.range Dτ.mulVecLin := by sorry
--| 1.7
  have hker : (∀ v ∈ LinearMap.range D.mulVecLin, y ⬝ᵥ v = 0) ∧ y s ≠ 0 ∧
      (Pi.single s (1 : ℝ) : I → ℝ) ∉ LinearMap.range D.mulVecLin := by sorry
--| 1.8
  have hrank : Dτ.rank > D.rank := by sorry
--| 1.9
  exact absurd (hmax Dτ hsupp) (not_le.mpr hrank)
