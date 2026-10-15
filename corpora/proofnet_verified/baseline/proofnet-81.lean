import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $G_1$ and $G_2$ are cyclic groups of orders $m$ and $n$, respectively, prove that $G_1 \times G_2$ is cyclic if and only if $m$ and $n$ are relatively prime.
-/

/-Informal Proof

The order of $G \times H$ is $n$. $m$. Thus, $G \times H$ is cyclic iff it has an element with order n. $m$. Suppose $\operatorname{gcd}(n . m)=1$. This implies that $g^m$ has order $n$, and analogously $h^n$ has order $m$. That is, $g \times h$ has order $n$. $m$, and therefore $G \times H$ is cyclic.

Suppose now that $\operatorname{gcd}(n . m)>1$. Let $g^k$ be an element of $G$ and $h^j$ be an element of $H$. Since the lowest common multiple of $n$ and $m$ is lower than the product $n . m$, that is, $\operatorname{lcm}(n, m)<n$. $m$, and since $\left(g^k\right)^{l c m(n, m)}=e_G,\left(h^j\right)^{l c m(n, m)}=e_H$, we have $\left(g^k \times h^j\right)^{l c m(n, m)}=e_{G \times H}$. It follows that every element of $G \times H$ has order lower than $n . m$, and therefore $G \times H$ is not cyclic.
-/

theorem Herstein_exercise_2_9_2 {G H : Type*} [Fintype G] [Fintype H] [Group G]
  [Group H] (hG : IsCyclic G) (hH : IsCyclic H) :
  IsCyclic (G × H) ↔ (card G).Coprime (card H) := by
  -- Step 1: split the desired equivalence into the two directions.
  constructor
  · -- Step 2: assume that the direct product is cyclic.
    intro hProd
    -- Step 3: unpack the general criterion for cyclicity of a product from mathlib.
    obtain ⟨-, -, hCoprimeNat⟩ :=
      (Group.isCyclic_prod_iff (M := G) (N := H)).1 hProd
    -- Step 4: convert the coprimality statement from `Nat.card` to the usual `Fintype.card`.
    -- Step 4.1: the rewrite uses that `Nat.card` agrees with `Fintype.card` on finite types.
    -- Step 4.2: the `simp` call performs this rewrite on both factors simultaneously.
    simpa [Nat.card_eq_fintype_card] using hCoprimeNat
  · -- Step 5: assume the cardinalities of the factors are coprime.
    intro hCoprime
    -- Step 6: rewrite the hypothesis so that it matches the format of the general criterion.
    have hCoprimeNat : (Nat.card G).Coprime (Nat.card H) := by
      -- Step 6.1: again rewrite the statement via the identification of the two cardinal notions.
      simpa [Nat.card_eq_fintype_card] using hCoprime
    -- Step 7: apply the general criterion together with the cyclicity of the factors.
    -- Step 7.1: the lemma transforms the triple of facts into the cyclicity of the product.
    exact (Group.isCyclic_prod_iff (M := G) (N := H)).2 ⟨hG, hH, hCoprimeNat⟩
