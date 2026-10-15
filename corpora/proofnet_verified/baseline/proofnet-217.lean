import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that $A \times B$ is an abelian group if and only if both $A$ and $B$ are abelian.
-/

/-Informal Proof

$(\Rightarrow)$ Suppose $a_1, a_2 \in A$ and $b_1, b_2 \in B$. Then
$$
\left(a_1 a_2, b_1 b_2\right)=\left(a_1, b_1\right) \cdot\left(a_2, b_2\right)=\left(a_2, b_2\right) \cdot\left(a_1, b_1\right)=\left(a_2 a_1, b_2 b_1\right) .
$$
Since two pairs are equal precisely when their corresponding entries are equal, we have $a_1 a_2=a_2 a_1$ and $b_1 b_2=b_2 b_1$. Hence $A$ and $B$ are abelian.
$(\Leftarrow)$ Suppose $\left(a_1, b_1\right),\left(a_2, b_2\right) \in A \times B$. Then we have
$$
\left(a_1, b_1\right) \cdot\left(a_2, b_2\right)=\left(a_1 a_2, b_1 b_2\right)=\left(a_2 a_1, b_2 b_1\right)=\left(a_2, b_2\right) \cdot\left(a_1, b_1\right) .
$$
Hence $A \times B$ is abelian.
-/

theorem Dummit_Foote_exercise_1_1_29 {A B : Type*} [Group A] [Group B] :
  (∀ x y : A × B, x * y = y * x) ↔ (∀ x y : A, x * y = y * x) ∧
  (∀ x y : B, x * y = y * x) := by
  -- Step 1: Split the biconditional into the two required directions.
  constructor
  · -- Step 1.1: Assume the direct product is abelian and deduce that each factor is abelian.
    intro hAB
    -- Step 1.1.1: Build the pair of goals showing A and B are abelian.
    constructor
    · -- Step 1.1.1.1: Fix arbitrary elements of A.
      intro a₁ a₂
      -- Step 1.1.1.2: Apply commutativity in the product to specially chosen elements.
      have hProj := congrArg Prod.fst (hAB ⟨a₁, (1 : B)⟩ ⟨a₂, 1⟩)
      -- Step 1.1.1.3: Simplify the first projection to obtain commutativity in A.
      simpa using hProj
    · -- Step 1.1.2.1: Fix arbitrary elements of B.
      intro b₁ b₂
      -- Step 1.1.2.2: Use product commutativity on elements supported in the B-coordinate.
      have hProj := congrArg Prod.snd (hAB ⟨(1 : A), b₁⟩ ⟨1, b₂⟩)
      -- Step 1.1.2.3: Simplify the second projection to obtain commutativity in B.
      simpa using hProj
  · -- Step 2: Assume each factor is abelian and prove the product is abelian.
    intro hFactors
    -- Step 2.1: Unpack the hypotheses that A and B are abelian.
    rcases hFactors with ⟨hA, hB⟩
    -- Step 2.2: Consider arbitrary elements of the direct product.
    intro x y
    -- Step 2.3: Break the product elements into their coordinates.
    rcases x with ⟨a₁, b₁⟩
    rcases y with ⟨a₂, b₂⟩
    -- Step 2.4: Reduce the equality in the product to equalities in each coordinate.
    ext
    · -- Step 2.4.1: The equality of first coordinates follows from hA.
      simpa using hA a₁ a₂
    · -- Step 2.4.2: The equality of second coordinates follows from hB.
      simpa using hB b₁ b₂
