import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Prove that if a group contains exactly one element of order 2 , then that element is in the center of the group.
-/

/-Informal Proof

Let $x$ be the element of order two. Consider the element $z=y^{-1} x y$, we have: $z^2=\left(y^{-1} x y\right)^2=\left(y^{-1} x y\right)\left(y^{-1} x y\right)=e$. So: $z=x$, and $y^{-1} x y=x$. So: $x y=y x$. So: $x$ is in the center of $G$.
-/

theorem Artin_exercise_2_4_19 {G : Type*} [Group G] {x : G}
  (hx : orderOf x = 2) (hx1 : ∀ y, orderOf y = 2 → y = x) :
  x ∈ center G := by
  -- Step 1: Switch to classical logic so that we can freely use choice and case distinctions.
  classical
  -- Step 2: Express membership in the center as the universal commuting property.
  refine (Subgroup.mem_center_iff.mpr ?_)
  -- Step 2.1: Fix an arbitrary element `g` whose commutativity with `x` we must verify.
  intro g
  -- Step 3: Observe that conjugation by `g` produces the element `g⁻¹ * x * g`.
  --         This element is semiconjugate to `x` via `g⁻¹`.
  have h_semiconj : SemiconjBy g⁻¹ x (g⁻¹ * x * g) := by
    -- Step 3.1: Unfold the definition of `SemiconjBy` and simplify the resulting expression.
    change g⁻¹ * x = g⁻¹ * x * g * g⁻¹
    -- Step 3.1.1: Associativity plus the inverse law collapses the right-hand side.
    simp [mul_assoc]
  -- Step 4: Conclude that conjugation preserves the order of `x`.
  have h_order_eq : orderOf x = orderOf (g⁻¹ * x * g) :=
    SemiconjBy.orderOf_eq (a := g⁻¹) (x := x) (y := g⁻¹ * x * g) h_semiconj
  -- Step 4.1: Translate the known order of `x` to the order of its conjugate.
  have h_conj_order : orderOf (g⁻¹ * x * g) = 2 := by
    -- Step 4.1.1: Rewrite the statement `orderOf x = 2` using `h_order_eq`.
    simpa [h_order_eq] using hx
  -- Step 5: Invoke the uniqueness hypothesis to identify the conjugate with `x` itself.
  have h_conj_eq : g⁻¹ * x * g = x := hx1 _ h_conj_order
  -- Step 6: Convert the conjugation equality into the desired commutativity relation.
  have h_comm : g * x = x * g := by
    -- Step 6.1: Multiply the equality on the left by `g` and simplify.
    have h_mul := congrArg (fun z => g * z) h_conj_eq
    -- Step 6.1.1: Simplifying shows that both sides are the same product.
    simpa [mul_assoc] using h_mul.symm
  -- Step 7: Finish by supplying the commuting equality (with the required orientation).
  exact h_comm
