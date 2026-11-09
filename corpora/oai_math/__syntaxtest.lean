import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.Ring.Defs

variable {I J : Type*} [Fintype I] [Fintype J]

def SupportedOn (T : Set (I × J)) (D : Matrix I J ℝ) : Prop :=
  ∀ s j, (s, j) ∉ T → D s j = 0

open Lean Elab Command in
run_cmd do
  let trees := (← get).infoState.trees
  trees.forM fun t => do
    t.visitM (preNode := fun ci info _ => do
      match info with
      | .ofTermInfo ti =>
        if let some r := info.stx.getRange? then
          -- is this a bound variable (fvar) occurrence? print its range + the expr it elaborated to
          match ti.expr with
          | .fvar fid => IO.println s!"FVAR occ [{r.start.byteIdx}..{r.stop.byteIdx}] -> {(← fid.getUserName)}"
          | _ => pure ()
      | _ => pure ()) |>.run' {} {}
