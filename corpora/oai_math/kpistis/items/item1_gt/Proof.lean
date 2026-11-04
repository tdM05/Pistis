/-
The GT counterpart of `kpistis/items/item1/Proof.lean`, read off `_gt/MaxSupportKernel.lean`
(`corpora/oai_math/items/item1/_gt/MaxSupportKernel.lean`) with its three theorems flattened into
one proof and cut into the SAME `--|` regions, so the two trees (`units/item1` and `units/item1_gt`)
can be compared edge for edge against the identical NL side.

Three liberties, all mechanical, none mathematical:
* `range_lt_range_add_single` and `kernel_support_of_max_rank` are inlined into `kernel_support`'s
  body — GT only ever calls the first from the second and the second from the third, so nothing is
  lost by writing the one chain GT already executes.
* every step body is `sorry` (as in `items/item1/Proof.lean`): only the STATEMENTS are being aligned.
* GT's local `let E := D + Matrix.single s j 1` / `let e := Pi.single s 1` are unfolded at their
  uses, so each `have`'s STATEMENT is self-contained and nameable as a region without a separate
  "formal context" item — see `kpistis/README.md`, *No formal context*.

Nothing else is changed: in particular `D + Matrix.single s j (1 : ℝ)` — not `D + τ • Matrix.single s
j (1 : ℝ)` for a bound `τ` — is GT's own term, copied verbatim. That absence of `τ` is exactly the
first finding in `items/item1/ai.md`, and the point of this file is to let `kpistis/check.py` locate
it on an edge instead of in prose.
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
  by_contra hxy
--| early-hxj
  have hxj : x j ≠ 0 := by sorry
--| early-hys
  have hys : y s ≠ 0 := by sorry
--| 1.2
  have hsupport : SupportedOn T (D + Matrix.single s j (1 : ℝ)) := by sorry
--| 1.3
  have hEx : (D + Matrix.single s j (1 : ℝ)).mulVec x
      = x j • (Pi.single s (1 : ℝ) : I → ℝ) := by sorry
--| 1.4
  have he : (Pi.single s (1 : ℝ) : I → ℝ) ∈
      LinearMap.range (D + Matrix.single s j (1 : ℝ)).mulVecLin := by sorry
--| 1.6
  have hle : LinearMap.range D.mulVecLin ≤
      LinearMap.range (D + Matrix.single s j (1 : ℝ)).mulVecLin := by sorry
--| 1.7
  have hnot : (Pi.single s (1 : ℝ) : I → ℝ) ∉ LinearMap.range D.mulVecLin := by sorry
--| 1.8
  have hlt : D.rank < (D + Matrix.single s j (1 : ℝ)).rank := by sorry
--| 1.9
  exact (not_lt_of_ge (hmax _ hsupport)) hlt
