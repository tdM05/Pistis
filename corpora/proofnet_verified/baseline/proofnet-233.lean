import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that there exists a normal subgroup that is not characteristic.
-/

/-Informal Proof

We have to produce a group $G$ and a subgroup $H$ such that $H$ is normal in $G$, but not characteristic. Consider the Klein's four group $G=\{ e, a, b, a b\}$. This is an abelian group with each element having order 2. Consider $H=\{ e, a\}$. $H$ is normal in $G$. Define $\sigma: G \rightarrow G$ as $\sigma(a)=b, \sigma(b)=a, \sigma(a b)=a b$. Clearly $\sigma$ does not fix $H$. So, $H$ is not characteristic.
-/

theorem Dummit_Foote_exercise_4_4_6b :
  ∃ (G : Type*) (hG : Group G) (H : @Subgroup G hG), @Normal G hG H ∧ ¬ @Characteristic G hG H := by
  classical
  -- Step 1: Choose the Klein four group and move it to a higher universe using `ULift`.
  let Base : Type := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
  -- Step 2: Record the group structure that `ULift` inherits from the base group.
  let _ : Group (ULift Base) := inferInstance
  -- Step 3: Define the subgroup consisting of elements whose second coordinate (downstairs) is the identity.
  let H : Subgroup (ULift Base) :=
    { carrier := {x : ULift Base | x.down.2 = 1},
      one_mem' := by
        -- Step 3.1: The lifted identity has second coordinate equal to `1`.
        simp [Set.mem_setOf_eq],
      mul_mem' := by
        -- Step 3.2: Closure under multiplication follows from coordinatewise multiplication in the direct product.
        intro a b ha hb
        have ha' : a.down.2 = 1 := ha
        have hb' : b.down.2 = 1 := hb
        change (a.down.2 * b.down.2) = 1
        simp [ha', hb'],
      inv_mem' := by
        -- Step 3.3: Inverses preserve the property because `1` is its own inverse in `ℤ/2ℤ`.
        intro a ha
        have ha' : a.down.2 = 1 := ha
        change (a.down.2)⁻¹ = 1
        simp [ha'] }
  -- Step 4: Introduce the coordinate-swapping automorphism on the lifted group.
  let swap : MulAut (ULift Base) :=
    { toFun := fun x : ULift Base => ⟨(x.down.2, x.down.1)⟩,
      invFun := fun x : ULift Base => ⟨(x.down.2, x.down.1)⟩,
      left_inv := by
        -- Step 4.0.1: Swapping twice returns the original element.
        intro x
        cases' x with x
        cases' x with a b
        simp,
      right_inv := by
        -- Step 4.0.2: The same reasoning applies from the codomain side.
        intro x
        cases' x with x
        cases' x with a b
        simp,
      map_mul' := by
        -- Step 4.0.3: Swapping commutes with multiplication because multiplication is coordinatewise.
        intro x y
        cases' x with x
        cases' y with y
        cases' x with a b
        cases' y with c d
        rfl }
  -- Step 4.1: Pick a specific element whose second coordinate is `1` but whose first coordinate is nontrivial.
  let witness : ULift Base := ⟨(Multiplicative.ofAdd (1 : ZMod 2), (1 : Multiplicative (ZMod 2)))⟩
  -- Step 4.2: Verify that this element indeed lies in the subgroup by construction.
  have witness_mem : witness ∈ H := by
    -- Step 4.2.1: Membership amounts to checking the second coordinate of `witness.down`.
    simp [H, witness, Set.mem_setOf_eq]
  -- Step 4.3: Show that the element leaves the subgroup after applying the swap automorphism.
  have witness_not_mem :
      witness ∉ H.comap swap.toMonoidHom := by
    -- Step 4.3.1: `Multiplicative.ofAdd 1` is not the identity element.
    have hne :
        Multiplicative.ofAdd (1 : ZMod 2) ≠ (1 : Multiplicative (ZMod 2)) := by
      change (1 : ZMod 2) ≠ 0
      decide
    -- Step 4.3.2: Translate eventual membership in the comap into a contradiction on second coordinates.
    intro hmem
    have hx_in_H : swap.toMonoidHom witness ∈ H := by
      simpa [Subgroup.mem_comap] using hmem
    have hx_second_one :
        (swap.toMonoidHom witness).down.2 = 1 := by
      simpa [H, Set.mem_setOf_eq]
    have hx_second_value :
        (swap.toMonoidHom witness).down.2 = Multiplicative.ofAdd (1 : ZMod 2) := by
      simp [swap, witness]
    exact hne (hx_second_value.symm.trans hx_second_one)
  -- Step 5: Assemble the data required by the existential quantifiers.
  refine ⟨ULift Base, inferInstance, H, ?_, ?_⟩
  · -- Step 5.1: Every subgroup of this abelian group is normal.
    exact inferInstance
  · -- Step 5.2: Use the automorphism `swap` to show that the subgroup cannot be characteristic.
    intro hChar
    have hFix := hChar.fixed swap
    have hwEq :=
      congrArg (fun K : Subgroup (ULift Base) => witness ∈ K) hFix
    exact witness_not_mem (hwEq.mpr witness_mem)
