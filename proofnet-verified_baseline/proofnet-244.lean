import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators nonZeroDivisors



/-Informal Statement

Let $p(x)=a_{n} x^{n}+a_{n-1} x^{n-1}+\cdots+a_{1} x+a_{0}$ be an element of the polynomial ring $R[x]$. Prove that $p(x)$ is a zero divisor in $R[x]$ if and only if there is a nonzero $b \in R$ such that $b p(x)=0$.
-/

/-Informal Proof

Solution: If $b p(x)=0$ for some nonzero $b \in R$, then it is clear that $p(x)$ is a zero divisor.
Now suppose $p(x)$ is a zero divisor; that is, for some $q(x)=\sum_{i=0}^m b_i x^i$, we have $p(x) q(x)=0$. We may choose $q(x)$ to have minimal degree among the nonzero polynomials with this property.
We will now show by induction that $a_i q(x)=0$ for all $0 \leq i \leq n$.
For the base case, note that
$$
p(x) q(x)=\sum_{k=0}^{n+m}\left(\sum_{i+j=k} a_i b_j\right) x^k=0 .
$$
The coefficient of $x^{n+m}$ in this product is $a_n b_m$ on one hand, and 0 on the other. Thus $a_n b_m=0$. Now $a_n q(x) p(x)=0$, and the coefficient of $x^m$ in $q$ is $a_n b_m=0$. Thus the degree of $a_n q(x)$ is strictly less than that of $q(x)$; since $q(x)$ has minimal degree among the nonzero polynomials which multiply $p(x)$ to 0 , in fact $a_n q(x)=0$. More specifically, $a_n b_i=0$ for all $0 \leq i \leq m$.
For the inductive step, suppose that for some $0 \leq t<n$, we have $a_r q(x)=0$ for all $t<r \leq n$. Now
$$
p(x) q(x)=\sum_{k=0}^{n+m}\left(\sum_{i+j=k} a_i b_j\right) x^k=0 .
$$
On one hand, the coefficient of $x^{m+t}$ is $\sum_{i+j=m+t} a_i b_j$, and on the other hand, it is 0 . Thus
$$
\sum_{i+j=m+t} a_i b_j=0 .
$$
By the induction hypothesis, if $i \geq t$, then $a_i b_j=0$. Thus all terms such that $i \geq t$ are zero. If $i<t$, then we must have $j>m$, a contradiction. Thus we have $a_t b_m=0$. As in the base case,
$$
a_t q(x) p(x)=0
$$
and $a_t q(x)$ has degree strictly less than that of $q(x)$, so that by minimality, $a_t q(x)=0$.
By induction, $a_i q(x)=0$ for all $0 \leq i \leq n$. In particular, $a_i b_m=0$. Thus $b_m p(x)=0$.
-/

theorem Dummit_Foote_exercise_7_2_2 {R : Type*} [Ring R] (p : Polynomial R) :
  p ∣ 0 ↔ ∃ b : R, b ≠ 0 ∧ b • p = 0 := by
  sorry

/-
Step 1: Record why the formal statement fails.
We take `R = ℤ` and `p = X`.  The equation `p ∣ 0` is always true (use the zero
multiplier), but no nonzero integer annihilates `X` coefficient-wise.  Hence the
equivalence collapses.
-/

namespace ProofNet244

lemma smul_X_eq_zero_iff (b : ℤ) :
    b • (Polynomial.X : Polynomial ℤ) = 0 ↔ b = 0 := by
  constructor
  · intro h
    -- Step 1: rewrite the scalar action using constant polynomials.
    have hC :
        (Polynomial.C (b : ℤ) : Polynomial ℤ) * Polynomial.X = 0 := by
      simpa [Polynomial.smul_eq_C_mul] using h
    -- Step 2: `Polynomial ℤ` is an integral domain, so the product splits.
    have hsplit := mul_eq_zero.mp hC
    -- Step 3: `X` is not zero, so the constant factor must vanish.
    have hconst :
        (Polynomial.C (b : ℤ) : Polynomial ℤ) = 0 :=
      hsplit.resolve_right Polynomial.X_ne_zero
    -- Step 4: translate back to integers.
    simpa using (Polynomial.C_eq_zero).1 hconst
  · intro hb
    -- Step 5: conversely, zero scalars certainly kill `X`.
    simp [hb]

theorem Dummit_Foote_exercise_7_2_2_neg :
    ¬ ((Polynomial.X : Polynomial ℤ) ∣ (0 : Polynomial ℤ) ↔
        ∃ b : ℤ, b ≠ 0 ∧ b • (Polynomial.X : Polynomial ℤ) = 0) := by
  classical
  -- Step 1: `X` divides `0` via the zero polynomial.
  have hdiv : (Polynomial.X : Polynomial ℤ) ∣ (0 : Polynomial ℤ) := by
    refine ⟨0, ?_⟩
    simp
  -- Step 2: show that no nonzero integer annihilates `X`.
  have hno :
      ¬ ∃ b : ℤ, b ≠ 0 ∧ b • (Polynomial.X : Polynomial ℤ) = 0 := by
    intro h
    rcases h with ⟨b, hb, hkill⟩
    have : b = 0 := (smul_X_eq_zero_iff b).1 hkill
    exact hb this
  -- Step 3: deduce that the proposed equivalence cannot hold.
  intro hiff
  exact hno (hiff.mp hdiv)

/-
Step 2: Provide a corrected (always true) statement.
Corrected version:
The original uses `p ∣ 0`, which is always true (take the zero multiplier)
and so does not characterize being a zero divisor.  The proper notion is
the existence of a nonzero polynomial multiplier `q` with `p * q = 0`.
With that definition, the biconditional of the informal statement does
hold: `p` is a zero divisor in `R[x]` iff some nonzero scalar `b ∈ R`
annihilates `p`.  The hard direction is the McCoy theorem, available in
Mathlib as `Polynomial.notMem_nonZeroDivisors_iff`.
-/

theorem Dummit_Foote_exercise_7_2_2_corrected {R : Type*} [CommRing R] (p : Polynomial R) :
    (∃ q : Polynomial R, q ≠ 0 ∧ p * q = 0) ↔
      (∃ b : R, b ≠ 0 ∧ b • p = 0) := by
  classical
  constructor
  · -- Forward direction: McCoy's theorem.
    -- Step 1: unpack the polynomial witness and flip the product.
    rintro ⟨q, hq, hpq⟩
    have hqp : q * p = 0 := by rw [mul_comm]; exact hpq
    -- Step 2: phrase `p` being a zero divisor via `nonZeroDivisors`.
    have hnot : p ∉ (Polynomial R)⁰ :=
      notMem_nonZeroDivisors_iff_right.mpr ⟨q, hqp, hq⟩
    -- Step 3: apply the McCoy theorem to extract a scalar annihilator.
    exact Polynomial.notMem_nonZeroDivisors_iff.mp hnot
  · -- Backward direction: the constant polynomial `C b` is the witness.
    rintro ⟨b, hb, hbp⟩
    refine ⟨Polynomial.C b, ?_, ?_⟩
    · -- Step 1: `C b ≠ 0` because `b ≠ 0` and `C` is injective at zero.
      intro hzero
      exact hb (Polynomial.C_eq_zero.mp hzero)
    · -- Step 2: `p * C b = C b * p = b • p = 0`.
      have hconst : (Polynomial.C b : Polynomial R) * p = 0 := by
        rw [← Polynomial.smul_eq_C_mul]; exact hbp
      rw [mul_comm]; exact hconst

end ProofNet244
