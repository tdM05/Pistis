import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $G$ is a finite group, prove that there is an integer $m > 0$ such that $a^m = e$ for all $a \in G$.
-/

/-Informal Proof

Let $n_1, n_2, \ldots, n_k$ be the orders of all $k$ elements of $G=$ $\left\{a_1, a_2, \ldots, a_k\right\}$. Let $m=\operatorname{lcm}\left(n_1, n_2, \ldots, n_k\right)$. Then, for any $i=$ $1, \ldots, k$, there exists an integer $c$ such that $m=n_i c$. Thus
$$
a_i^m=a_i^{n_i c}=\left(a_i^{n_i}\right)^c=e^c=e
$$
Hence $m$ is a positive integer such that $a^m=e$ for all $a \in G$.
-/

theorem Herstein_exercise_2_1_27 {G : Type*} [Group G]
  [Fintype G] : ∃ (m : ℕ), m > 0 ∧ ∀ (a : G), a ^ m = 1 := by
  -- Step 1: Choose a concrete candidate for `m` by taking the number of elements of `G`.
  refine ⟨Fintype.card G, ?_, ?_⟩
  -- Step 2: Prove that this chosen `m` is strictly positive.
  -- Step 2.1: Exhibit an explicit element of `G` (namely `1`) to show that `G` is nonempty.
  -- Step 2.2: Apply `Fintype.card_pos_iff` to turn that witness into the desired positivity.
  ·
    have h_nonempty : Nonempty G := ⟨(1 : G)⟩
    exact Fintype.card_pos_iff.mpr h_nonempty
  -- Step 3: Show that every element raised to the `m`th power equals the identity.
  -- Step 3.1: Fix an arbitrary element `a : G`.
  -- Step 3.2: Use the standard result `pow_card_eq_one` for finite groups.
  · intro a
    exact pow_card_eq_one (G := G) (x := a)
