import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Let $K$ be a finite field. Prove that the product of the nonzero elements of $K$ is $-1$.
-/

/-Informal Proof

Since we are working with a finite field with $q$ elements, anyone of them is a root of the following polynomial
$$
x^q-x=0 .
$$
In particular if we rule out the 0 element, any $a_i \neq 0$ is a root of
$$
x^{q-1}-1=0 .
$$
This polynomial splits completely in $\mathbb{F}_q$ so we find
$$
\left(x-a_1\right) \cdots\left(x-a_{q-1}\right)=0
$$
in particular
$$
x^{q-1}-1=\left(x-a_1\right) \cdots\left(x-a_{q-1}\right)
$$
Thus $a_1 \cdots a_{q-1}=-1$.
-/

theorem Artin_exercise_13_6_10 {K : Type*} [Field K] [Fintype Kˣ] :
  (∏ x : Kˣ,  x) = -1 := by
  -- Step 1: Switch to classical logic so that we can freely use choice-based lemmas about finite fields.
  classical
  -- Step 2: Apply the ready-made finite field lemma stating that the product of all units is `-1`.
  --         This lemma already works under the hypotheses `[CommRing K] [IsDomain K] [Fintype Kˣ]`,
  --         which are satisfied here because every field is a commutative ring and an integral domain.
  have h : (∏ x : Kˣ, x) = (-1 : Kˣ) :=
    FiniteField.prod_univ_units_id_eq_neg_one (K := K)
  -- Step 3: Our goal matches the lemma exactly, so we conclude by a simple rewriting step.
  simpa using h
