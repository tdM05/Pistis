import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $G$ is a finite group, prove that, given $a \in G$, there is a positive integer $n$, depending on $a$, such that $a^n = e$.
-/

/-Informal Proof

Because there are only a finite number of elements of $G$, it's clear that the set $\left\{a, a^2, a^3, \ldots\right\}$ must be a finite set and in particular, there should exist some $i$ and $j$ such that $i \neq j$ and $a^i=a^j$. WLOG suppose further that $i>j$ (just reverse the roles of $i$ and $j$ otherwise). Then multiply both sides by $\left(a^j\right)^{-1}=a^{-j}$ to get
$$
a^i * a^{-j}=a^{i-j}=e
$$
Thus the $n=i-j$ is a positive integer such that $a^n=e$.
-/

theorem Herstein_exercise_2_1_26 {G : Type*} [Group G]
  [Fintype G] (a : G) : ∃ (n : ℕ), n > 0 ∧ a ^ n = 1 := by
  classical
  -- Step 1: Establish that the finite type `G` has strictly positive cardinality.
  have h_card_pos : 0 < Fintype.card G := by
    -- Step 1.1: Use the generic lemma `Fintype.card_pos` (applicable because `G` has the identity element)
    --           to conclude that every finite group contains at least one element, so its cardinality is positive.
    exact Fintype.card_pos
  -- Step 2: Choose the natural number `n` to be the total number of elements of `G`.
  refine ⟨Fintype.card G, h_card_pos, ?_⟩
  -- Step 3: Apply the standard lemma `pow_card_eq_one`, which encodes the pigeonhole/Lagrange argument
  --         and guarantees that raising any element of a finite group to `|G|` gives the identity.
  -- Step 3.1: Specialize the lemma to the element `a` under study to conclude the proof.
  exact pow_card_eq_one (G := G) (x := a)
