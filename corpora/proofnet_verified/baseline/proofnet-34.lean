import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

If $x$ is an element of infinite order in $G$, prove that the elements $x^{n}, n \in \mathbb{Z}$ are all distinct.
-/

/-Informal Proof

Solution: Suppose to the contrary that $x^a=x^b$ for some $0 \leq a<b \leq n-1$. Then we have $x^{b-a}=1$, with $1 \leq b-a<n$. However, recall that $n$ is by definition the least integer $k$ such that $x^k=1$, so we have a contradiction. Thus all the $x^i$, $0 \leq i \leq n-1$, are distinct. In particular, we have
$$
\left\{x^i \mid 0 \leq i \leq n-1\right\} \subseteq G,
$$
so that $|x|=n \leq|G|$
-/

theorem Dummit_Foote_exercise_1_1_34 {G : Type*} [Group G] {x : G}
  (hx_inf : orderOf x = 0) (n m : ℤ) (hnm : n ≠ m) :
  x ^ n ≠ x ^ m := by
  -- Step 1: Translate the hypothesis `orderOf x = 0` into the fact that `x` has infinite order.
  have hx_not_fin : ¬IsOfFinOrder x := by
    -- Step 1.1: Use the characterization of infinite order via `orderOf x = 0`.
    exact (orderOf_eq_zero_iff (x := x)).1 hx_inf
  -- Step 2: Deduce that the map `ℤ → G`, `n ↦ x ^ n`, is injective because `x` has infinite order.
  have hx_inj : Function.Injective fun k : ℤ => x ^ k :=
    -- Step 2.1: Apply the injectivity criterion that holds precisely when the element has infinite order.
    (injective_zpow_iff_not_isOfFinOrder (x := x)).2 hx_not_fin
  -- Step 3: Prove the desired inequality by contradiction.
  intro h_eq
  -- Step 3.1: Injectivity forces the exponents to coincide whenever the powers coincide.
  have h_nm : n = m := hx_inj h_eq
  -- Step 3.2: The obtained equality contradicts the initial assumption that `n` and `m` differ.
  exact hnm h_nm
