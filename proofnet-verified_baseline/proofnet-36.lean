import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $G$ be any group. Prove that the map from $G$ to itself defined by $g \mapsto g^{-1}$ is a homomorphism if and only if $G$ is abelian.
-/

/-Informal Proof

$(\Rightarrow)$ Suppose $G$ is abelian. Then
$$
\varphi(a b)=(a b)^{-1}=b^{-1} a^{-1}=a^{-1} b^{-1}=\varphi(a) \varphi(b),
$$
so that $\varphi$ is a homomorphism.
$(\Leftarrow)$ Suppose $\varphi$ is a homomorphism, and let $a, b \in G$. Then
$$
a b=\left(b^{-1} a^{-1}\right)^{-1}=\varphi\left(b^{-1} a^{-1}\right)=\varphi\left(b^{-1}\right) \varphi\left(a^{-1}\right)=\left(b^{-1}\right)^{-1}\left(a^{-1}\right)^{-1}=b a,
$$
so that $G$ is abelian.
-/

theorem Dummit_Foote_exercise_1_6_17 {G : Type*} [Group G] (f : G → G)
  (hf : f = λ g => g⁻¹) :
  (∀ x y : G, f x * f y = f (x*y)) ↔ ∀ x y : G, x*y = y*x := by
  -- Step 1: Prove the forward direction (assuming the inversion map is a homomorphism).
  constructor
  · -- Step 1.1: Assume the homomorphism property for the function f.
    -- Step 1.2: Fix arbitrary elements x and y in G.
    intro hHom x y
    -- Step 1.3: Rewrite the homomorphism condition using the explicit formula for f.
    have hxy : x⁻¹ * y⁻¹ = (x * y)⁻¹ := by
      -- Step 1.3.1: Specialize the assumed homomorphism property to x and y.
      have hx := hHom x y
      -- Step 1.3.2: Replace every occurrence of f with the inversion map and simplify.
      simpa [hf] using hx
    -- Step 1.4: Invert the resulting equality to obtain information about x and y themselves.
    have hyx : y * x = x * y := by
      -- Step 1.4.1: Apply inversion to both sides of the equality on inverses.
      have hx_inv := congrArg Inv.inv hxy
      -- Step 1.4.2: Simplify the inverted equality to obtain the reversed product equality.
      simpa using hx_inv
    -- Step 1.5: Reorient the equality so that it matches the required direction x * y = y * x.
    exact (eq_comm.mp hyx)
  -- Step 2: Prove the backward direction (assuming G is abelian).
  · -- Step 2.1: Assume the group law is commutative.
    -- Step 2.2: Fix arbitrary elements x and y in G.
    intro hComm x y
    -- Step 2.3: Translate commutativity into an explicit formula for the inverse of a product.
    have h_inv_prod : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
      -- Step 2.3.1: Apply inversion to the commutativity witness.
      have h_xy := congrArg Inv.inv (hComm x y)
      -- Step 2.3.2: Simplify the inverted equality to isolate the inverses in order.
      simpa using h_xy
    -- Step 2.4: Use the obtained formula to verify the homomorphism condition.
    calc
      f x * f y
          = x⁻¹ * y⁻¹ := by
            -- Step 2.4.1: Replace f with the inversion map.
            simp [hf]
      _ = (x * y)⁻¹ := by
            -- Step 2.4.2: Replace with the inverse formula derived in Step 2.3.
            exact h_inv_prod.symm
      _ = f (x * y) := by
            -- Step 2.4.3: Express the inverse back in terms of f.
            simp [hf]
