import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Let $R$ be the ring of $2 \times 2$ matrices over the real numbers; suppose that $I$ is an ideal of $R$. Show that $I = (0)$ or $I = R$.
-/

/-Informal Proof

Suppose that $I$ is a nontrivial ideal of $R$, and let
$$
A=\left(\begin{array}{ll}
a & b \\
c & d
\end{array}\right)
$$
where not all of $a, b, c d$ are zero. Suppose, without loss of generality -- our steps would be completely analogous, modulo some different placement of 1 s in our matrices, if we assumed some other element to be nonzero -- that $a \neq 0$. Then we have that
$$
\left(\begin{array}{ll}
1 & 0 \\
0 & 0
\end{array}\right)\left(\begin{array}{ll}
a & b \\
c & d
\end{array}\right)=\left(\begin{array}{ll}
a & b \\
0 & 0
\end{array}\right) \in I
$$
and so
$$
\left(\begin{array}{ll}
a & b \\
0 & 0
\end{array}\right)\left(\begin{array}{ll}
1 & 0 \\
0 & 0
\end{array}\right)=\left(\begin{array}{ll}
a & 0 \\
0 & 0
\end{array}\right) \in I
$$
so that
$$
\left(\begin{array}{ll}
x & 0 \\
0 & 0
\end{array}\right) \in I
$$
for any real $x$. Now, also for any real $x$,
$$
\left(\begin{array}{ll}
x & 0 \\
0 & 0
\end{array}\right)\left(\begin{array}{ll}
0 & 1 \\
0 & 0
\end{array}\right)=\left(\begin{array}{ll}
0 & x \\
0 & 0
\end{array}\right) \in I .
$$
Likewise
$$
\left(\begin{array}{ll}
0 & 0 \\
1 & 0
\end{array}\right)\left(\begin{array}{ll}
0 & x \\
0 & 0
\end{array}\right)=\left(\begin{array}{ll}
0 & 0 \\
0 & x
\end{array}\right) \in I
$$
and
$$
\left(\begin{array}{ll}
0 & 0 \\
0 & x
\end{array}\right)\left(\begin{array}{ll}
0 & 0 \\
1 & 0
\end{array}\right)=\left(\begin{array}{ll}
0 & 0 \\
x & 0
\end{array}\right)
$$
Thus, as
$$
\left(\begin{array}{ll}
a & b \\
c & d
\end{array}\right)=\left(\begin{array}{ll}
a & 0 \\
0 & 0
\end{array}\right)+\left(\begin{array}{ll}
0 & b \\
0 & 0
\end{array}\right)+\left(\begin{array}{ll}
0 & 0 \\
c & 0
\end{array}\right)+\left(\begin{array}{ll}
0 & 0 \\
0 & d
\end{array}\right)
$$
and since all the terms on the right side are in $I$ and $I$ is an additive group, it follows that
$$
\left(\begin{array}{ll}
a & b \\
c & d
\end{array}\right)
$$
for arbitrary $a, b, c, d$ is in $I$, i.e. $I=R$
Note that the intuition for picking these matrices is that, if we denote by $E_{i j}$ the matrix with 1 at position $(i, j)$ and 0 elsewhere, then
$$
E_{i j}\left(\begin{array}{ll}
a_{1,1} & a_{1,2} \\
a_{2,1} & a_{2,2}
\end{array}\right) E_{n m}=a_{j, n} E_{i m}
$$
-/

theorem Herstein_exercise_4_3_25 (I : Ideal (Matrix (Fin 2) (Fin 2) ℝ)) :
  I = ⊥ ∨ I = ⊤ := by
  sorry

/-
Step 1: Record why the formal Lean statement fails.
Step 2: Exhibit a concrete counterexample ideal with zero second column.
Step 3: Use the counterexample to prove the negation of the original statement.
Step 4: Explain and prove a corrected version phrased with two-sided ideals.
-/

/-
Step 1: Explain the gap between the informal and formal versions.
Step 1.1: In Lean the type `Ideal` encodes left ideals, while the informal proof assumes
          two-sided ideals.
Step 1.2: Left ideals of the full matrix ring need not be trivial, so the formal claim is false.
-/
/-
Step 1: Written explanation of the failure of the original Lean statement.
-/
/-
Step 1: The informal argument proves that every **two-sided** ideal of the full matrix ring is
        either `⊥` or `⊤`.
Step 2: In Lean, `Ideal (Matrix (Fin 2) (Fin 2) ℝ)` denotes **left** ideals.
Step 3: The set of matrices whose second column is zero forms a nontrivial left ideal:
        - Step 3.1: It contains the nonzero idempotent `E_{0,0}` (the matrix with a single `1`
                  in the top-left corner).
        - Step 3.2: It is closed under left multiplication by arbitrary matrices, so it is an ideal.
        - Step 3.3: It omits the matrix `E_{0,1}`, hence it is proper.
Step 4: Therefore the Lean statement asserting that every `Ideal` is `⊥` or `⊤` is false.
-/

namespace Proofnet87

open scoped Matrix BigOperators

noncomputable section

local notation "ι₀" => (0 : Fin 2)
local notation "ι₁" => (1 : Fin 2)
local notation "E₀₀" => Matrix.single ι₀ ι₀ (1 : ℝ)
local notation "E₀₁" => Matrix.single ι₀ ι₁ (1 : ℝ)

/- Step 2: Define the left ideal consisting of matrices whose second column is zero. -/
def zeroSecondColumnIdeal : Ideal (Matrix (Fin 2) (Fin 2) ℝ) where
  carrier := {A | ∀ i, A i ι₁ = 0}
  zero_mem' := by
    -- Step 2.1: The zero matrix has zero entries everywhere, hence in particular in column `ι₁`.
    intro i
    -- Step 2.1.1: Evaluate the zero matrix entrywise.
    simp
  add_mem' := by
    -- Step 2.2: Column `ι₁` stays zero under addition.
    intro A B hA hB i
    -- Step 2.2.1: Expand the `(i, ι₁)` entry of the sum.
    simp [hA i, hB i]
  smul_mem' := by
    -- Step 2.3: Closure under left multiplication.
    intro M A hA i
    -- Step 2.3.1: Expand the `(i, ι₁)` entry of the product.
    -- Step 2.3.2: Each term in the sum is zero because the `ι₁`-column of `A` vanishes.
    classical
    have h0 : A ι₀ ι₁ = 0 := hA ι₀
    have h1 : A ι₁ ι₁ = 0 := hA ι₁
    simp [Matrix.mul_apply, h0, h1, Fin.sum_univ_two]

lemma zeroSecondColumnIdeal_contains_E₀₀ :
    E₀₀ ∈ zeroSecondColumnIdeal := by
  classical
  -- Step 2.4: Verify the defining property column-by-column.
  intro i
  -- Step 2.4.1: If `i = ι₀`, the `(ι₀, ι₁)` entry is zero because `ι₁ ≠ ι₀`.
  -- Step 2.4.2: Otherwise the entry is zero since `E₀₀` only has possibly nonzero entries in row `ι₀`.
  change Matrix.single ι₀ ι₀ (1 : ℝ) i ι₁ = 0
  by_cases hi : i = ι₀
  · subst hi
    simp [Matrix.single]
  ·
    have hrow : i ≠ ι₀ := hi
    simp [Matrix.single]

lemma second_column_zero_of_mem_zeroSecondColumnIdeal
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A ∈ zeroSecondColumnIdeal) :
    ∀ i : Fin 2, A i ι₁ = 0 := by
  -- Step 2.5: Immediate from the definition of membership.
  exact hA

lemma E₀₁_not_mem_zeroSecondColumnIdeal :
    E₀₁ ∉ zeroSecondColumnIdeal := by
  classical
  -- Step 2.7: Evaluate the `(0, 1)` entry, which equals `1`.
  have h := second_column_zero_of_mem_zeroSecondColumnIdeal (A := E₀₁)
  -- Step 2.8: Derive the contradiction via the explicit value.
  intro hmem
  -- Step 2.9: Specialize the zero-second-column property at `i = 0`.
  have hcol := h hmem ι₀
  -- Step 2.10: Simplify the specialized equality to `1 = 0`.
  have hcol' : (1 : ℝ) = 0 := by
    simp [Matrix.single] at hcol
  -- Step 2.11: Contradict the equality using `one_ne_zero`.
  exact (one_ne_zero hcol')

lemma zeroSecondColumnIdeal_ne_bot :
    zeroSecondColumnIdeal ≠ (⊥ : Ideal (Matrix (Fin 2) (Fin 2) ℝ)) := by
  classical
  -- Step 2.14: Show the generator is nonzero and lies in the ideal.
  intro h
  -- Step 2.15: Evaluate membership contradiction.
  have hmem := zeroSecondColumnIdeal_contains_E₀₀
  -- Step 2.16: Use the hypothesis `h` to rewrite the membership.
  have : E₀₀ ∈ (⊥ : Ideal (Matrix (Fin 2) (Fin 2) ℝ)) := by simpa [h] using hmem
  -- Step 2.17: The bottom ideal contains only the zero matrix.
  have hzero : E₀₀ = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
    -- Step 2.17.1: Unfold membership in the bottom ideal.
    simpa using this
  -- Step 2.18: The `(0, 0)` entry of `E₀₀` equals `1`, contradiction.
  have hentry : (1 : ℝ) = 0 := by
    -- Step 2.18.1: Evaluate the `(0, 0)` entry explicitly.
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M ι₀ ι₀) hzero
    simp [Matrix.single] at this
  -- Step 2.19: Finish by impossibility.
  exact one_ne_zero hentry

lemma zeroSecondColumnIdeal_ne_top :
    zeroSecondColumnIdeal ≠ (⊤ : Ideal (Matrix (Fin 2) (Fin 2) ℝ)) := by
  classical
  -- Step 2.20: Use the exclusion of `E₀₁`.
  intro h
  -- Step 2.21: Rewrite the supposed membership using `h`.
  have : E₀₁ ∈ zeroSecondColumnIdeal := by simp [h]
  -- Step 2.22: Contradict `E₀₁` not lying in the ideal.
  exact (E₀₁_not_mem_zeroSecondColumnIdeal this)

end

end Proofnet87

/-
Step 3: Convert the counterexample into a formal negation of the original statement.
-/

/-- Step 3: The original universal statement is false because of the zero-second-column ideal. -/
theorem Herstein_exercise_4_3_25_neg :
    ¬ (∀ I : Ideal (Matrix (Fin 2) (Fin 2) ℝ), I = ⊥ ∨ I = ⊤) := by
  classical
  -- Step 3.1: Assume the (false) universal claim holds.
  intro h
  -- Step 3.2: Plug in the counterexample ideal.
  have hI := h Proofnet87.zeroSecondColumnIdeal
  -- Step 3.3: Analyse the two cases separately.
  cases hI with
  | inl hbot =>
      -- Step 3.3.1: Contradict the equality `I = ⊥` using the earlier lemma.
      exact Proofnet87.zeroSecondColumnIdeal_ne_bot hbot
  | inr htop =>
      -- Step 3.3.2: Contradict the equality `I = ⊤` using the earlier lemma.
      exact Proofnet87.zeroSecondColumnIdeal_ne_top htop

/-
Step 4: State and prove the corrected version using two-sided ideals.
-/
/-
Step 4.1: Correction — when `I` ranges over `TwoSidedIdeal`, the statement becomes true.
Step 4.2: Proof outline — rely on the instance `[IsSimpleRing (Matrix (Fin 2) (Fin 2) ℝ)]`
          supplied by mathlib.
-/

/-- Step 4: Corrected version for two-sided ideals. -/
theorem Herstein_exercise_4_3_25_corrected
    (I : TwoSidedIdeal (Matrix (Fin 2) (Fin 2) ℝ)) :
    I = ⊥ ∨ I = ⊤ := by
  classical
  -- Step 4.1: Invoke the simple-ring structure of the full matrix ring.
  have hsimple :
      IsSimpleOrder (TwoSidedIdeal (Matrix (Fin 2) (Fin 2) ℝ)) :=
    IsSimpleRing.simple (R := Matrix (Fin 2) (Fin 2) ℝ)
  -- Step 4.2: Apply the `eq_bot_or_eq_top` property from the simple order.
  exact hsimple.eq_bot_or_eq_top _
