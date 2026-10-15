import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Let $I, J$ be ideals of a ring $R$ such that $I+J=R$. Prove that $I J=I \cap J$.
-/

/-Informal Proof

We have seen that $IJ \subset I \cap J$, so it remains to show that $I \cap J \subset IJ$.  Since $I+J = (1)$, there are elements $i \in I$ and $j \in J$ such that $i+j = 1$.  Let $k \in I \cap J$, and multiply $i+j=1$ through by $k$ to get $ki+kj = k$.  Write this more suggestively as
\[ k = ik+kj. \]
The first term is in $IJ$ because $k \in J$, and the second term is in $IJ$ because $k \in I$, so $k \in IJ$ as desired.
-/

theorem Artin_exercise_10_4_7a {R : Type*} [CommRing R]
  (I J : Ideal R) (hIJ : I + J = ⊤) : I * J = I ⊓ J := by
  classical
  -- Step 1: Reduce the goal to proving opposite inclusions of ideals.
  refine le_antisymm ?_ ?_
  -- Step 2: Use the general containment `I * J ≤ I ⊓ J`.
  · -- Step 2.1: Invoke the library lemma that packages the containment.
    exact Ideal.mul_le_inf
  -- Step 3: Deduce `I ⊓ J ≤ I * J` from the hypothesis `I + J = ⊤`.
  · -- Step 3.1: Turn the hypothesis into a Bézout identity inside the ring.
    have hUnit : I + J = (1 : Ideal R) := by
      -- Step 3.1.1: Express the unit ideal as the top ideal to reuse `hIJ`.
      simpa [one_eq_top] using hIJ
    have hCoprime : IsCoprime I J := (Ideal.isCoprime_iff_add).2 hUnit
    -- Step 3.1.2: Extract `i ∈ I` and `j ∈ J` with `i + j = 1`.
    obtain ⟨i, hi, j, hj, hij⟩ := hCoprime.exists
    -- Step 3.2: Take an arbitrary element of `I ⊓ J` and aim to show it lives in `I * J`.
    intro x hx
    -- Step 3.2.1: Separate the intersection membership into the two component memberships.
    obtain ⟨hxI, hxJ⟩ := Ideal.mem_inf.mp hx
    -- Step 3.3: Rewrite `x` using the decomposition of `1`.
    have hDecomp : x = x * i + x * j := by
      -- Step 3.3.1: Substitute `1 = i + j` and distribute the multiplication.
      calc
        x = x * 1 := (mul_one x).symm
        _ = x * (i + j) := by
          simp [hij]
        _ = x * i + x * j := by
          simp [mul_add]
    -- Step 3.4: Show each summand belongs to the product ideal.
    have hxMulI : x * i ∈ I * J := by
      -- Step 3.4.1: Commute the factors to apply `Ideal.mul_mem_mul`.
      simpa [mul_comm] using Ideal.mul_mem_mul hi hxJ
    have hxMulJ : x * j ∈ I * J := by
      -- Step 3.4.2: Apply the same idea with the other membership data.
      simpa [mul_comm] using Ideal.mul_mem_mul hxI hj
    -- Step 3.5: Additivity of ideals keeps the sum inside `I * J`.
    have hxSum : x * i + x * j ∈ I * J := (I * J).add_mem hxMulI hxMulJ
    -- Step 3.6: Substitute the decomposition of `x` to conclude membership.
    exact hDecomp.symm ▸ hxSum
