import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators InnerProductSpace



/-Informal Statement

Prove that $\left(\sum_{j=1}^{n} a_{j} b_{j}\right)^{2} \leq\left(\sum_{j=1}^{n} j a_{j}{ }^{2}\right)\left(\sum_{j=1}^{n} \frac{b_{j}{ }^{2}}{j}\right)$ for all real numbers $a_{1}, \ldots, a_{n}$ and $b_{1}, \ldots, b_{n}$.
-/

/-Informal Proof

Let $a_1, a_2, \ldots, a_n, b_1, b_2, \ldots, b_n \in R$.
We have that
$$
\left(\sum_{j=1}^n a_j b_j\right)^2
$$
is equal to the
$$
\left(\sum_{j=1}^n a_j b_j \frac{\sqrt{j}}{\sqrt{j}}\right)^2=\left(\sum_{j=1}^n\left(\sqrt{j} a_j\right)\left(b_j \frac{1}{\sqrt{j}}\right)\right)^2
$$
This can be observed as an inner product, and using the Cauchy-Schwarz Inequality, we get
$$
\begin{aligned}
&\left(\sum_{j=1}^n a_j b_j\right)^2=\left(\sum_{j=1}^n\left(\sqrt{j} a_j\right)\left(b_j \frac{1}{\sqrt{j}}\right)\right)^2 \\
&=\left\langle\left(a, \sqrt{2} a_2, \ldots, \sqrt{n} a_n\right),\left(b_1, \frac{b_2}{\sqrt{2}}, \ldots, \frac{b_n}{\sqrt{n}}\right)\right\rangle \\
& \leq\left\|\left(a, \sqrt{2} a_2, \ldots, \sqrt{n} a_n\right)\right\|^2\left\|\left(b_1, \frac{b_2}{\sqrt{2}}, \ldots, \frac{b_n}{\sqrt{n}}\right)\right\|^2 \\
&=\left(\sum_{j=1}^n j a_j^2\right)\left(\sum_{j=1}^n \frac{b_j^2}{j}\right) \\
& \text { Hence, }\left(\sum_{j=1}^n a_j b_j\right)^2=\left(\sum_{j=1}^n j a_j^2\right)\left(\sum_{j=1}^n \frac{b_j^2}{j}\right) .
\end{aligned}
$$
-/

theorem Axler_exercise_6_3 {n : ℕ} (a b : Fin n → ℝ) :
  (∑ i, a i * b i) ^ 2 ≤ (∑ i : Fin n, (i + 1) * a i ^ 2) * (∑ i, b i ^ 2 / (i + 1)) := by
  -- Step 1: Positivity facts for the weight (i + 1).
  have hpos : ∀ i : Fin n, (0 : ℝ) < (i.val : ℝ) + 1 := by
    intro i; positivity
  have hnn : ∀ i : Fin n, (0 : ℝ) ≤ (i.val : ℝ) + 1 := fun i => (hpos i).le
  have hsne : ∀ i : Fin n, Real.sqrt ((i.val : ℝ) + 1) ≠ 0 :=
    fun i => ne_of_gt (Real.sqrt_pos.2 (hpos i))
  -- Step 2: Apply discrete Cauchy–Schwarz with rescaled sequences.
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun (i : Fin n) => Real.sqrt ((i.val : ℝ) + 1) * a i)
    (fun (i : Fin n) => b i / Real.sqrt ((i.val : ℝ) + 1))
  -- Step 3: Show f i * g i = a i * b i.
  have hfg : ∀ i ∈ Finset.univ, (Real.sqrt ((i.val : ℝ) + 1) * a i) *
      (b i / Real.sqrt ((i.val : ℝ) + 1)) = a i * b i := by
    intro i _
    field_simp [hsne i]
  -- Step 4: Show f i ^ 2 = (i + 1) * a i ^ 2.
  have hf2 : ∀ i ∈ Finset.univ, (Real.sqrt ((i.val : ℝ) + 1) * a i) ^ 2 =
      ((i.val : ℝ) + 1) * a i ^ 2 := by
    intro i _
    rw [mul_pow, Real.sq_sqrt (hnn i)]
  -- Step 5: Show g i ^ 2 = b i ^ 2 / (i + 1).
  have hg2 : ∀ i ∈ Finset.univ, (b i / Real.sqrt ((i.val : ℝ) + 1)) ^ 2 =
      b i ^ 2 / ((i.val : ℝ) + 1) := by
    intro i _
    rw [div_pow, Real.sq_sqrt (hnn i)]
  -- Step 6: Rewrite Cauchy–Schwarz in terms of the original sequences.
  rw [Finset.sum_congr rfl hfg] at hcs
  rw [Finset.sum_congr rfl hf2, Finset.sum_congr rfl hg2] at hcs
  exact hcs
