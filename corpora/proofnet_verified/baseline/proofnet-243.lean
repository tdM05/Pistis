import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that any subring of a field which contains the identity is an integral domain.
-/

/-Informal Proof

Solution: Let $R \subseteq F$ be a subring of a field. (We need not yet assume that $1 \in R$ ). Suppose $x, y \in R$ with $x y=0$. Since $x, y \in F$ and the zero element in $R$ is the same as that in $F$, either $x=0$ or $y=0$. Thus $R$ has no zero divisors. If $R$ also contains 1 , then $R$ is an integral domain.
-/

theorem Dummit_Foote_exercise_7_1_12 {F : Type*} [Field F] {K : Subring F}
  (hK : (1 : F) ∈ K) : IsDomain K := by
  classical
  -- Step 1: Reduce the goal to proving `NoZeroDivisors K` and `Nontrivial K`.
  refine (isDomain_iff_noZeroDivisors_and_nontrivial (α := K)).2 ?_
  -- Step 1.1: Prove the two required components separately.
  refine ⟨?_, ?_⟩
  · -- Step 2: Establish that there are no zero divisors inside the subring `K`.
    refine ⟨?_⟩
    intro a b hMulZero
    -- Step 2.1: Push the product equation to the ambient field `F`.
    have hCoe :=
      congrArg (fun z : K => (z : F)) hMulZero
    -- Step 2.2: Rewrite the pushed equation as a product in `F`.
    have hProduct : (a : F) * (b : F) = 0 := by
      simpa using hCoe
    -- Step 2.3: Use the fact that the field `F` has no zero divisors.
    have hSplit : (a : F) = 0 ∨ (b : F) = 0 :=
      eq_zero_or_eq_zero_of_mul_eq_zero hProduct
    -- Step 2.4: Pull the disjunction back down to `K`.
    refine hSplit.elim ?left ?right
    · -- Step 2.4.1: If `(a : F) = 0`, then `a = 0` in `K`.
      intro ha
      left
      apply Subtype.ext
      -- Step 2.4.2: Equality in `F` forces equality in the subtype.
      simpa using ha
    · -- Step 2.4.3: If `(b : F) = 0`, then `b = 0` in `K`.
      intro hb
      right
      apply Subtype.ext
      -- Step 2.4.4: Equality in `F` again implies equality in `K`.
      simpa using hb
  · -- Step 3: Exhibit two distinct elements of `K` to prove `Nontrivial K`.
    refine ⟨⟨⟨0, K.zero_mem⟩, ⟨1, hK⟩, ?_⟩⟩
    -- Step 3.1: Show that the chosen zero and one are different inside `K`.
    intro hEq
    -- Step 3.2: Map the equality back to `F` and reach a contradiction with `zero_ne_one`.
    have hVal := congrArg (fun z : K => (z : F)) hEq
    change (0 : F) = 1 at hVal
    exact zero_ne_one hVal
