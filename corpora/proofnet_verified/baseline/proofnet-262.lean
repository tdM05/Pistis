import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Prove that a group of order 9 must be abelian.
-/

/-Informal Proof

We use the result from problem 40 which is as follows: Suppose $G$ is a group, $H$ is a subgroup and $|G|=n$ and $n \nmid\left(i_G(H)\right) !$. Then there exists a normal subgroup $\$ K \backslash$ neq $\{$ e $\} \$$ and $K \subseteq H$.
So, we have now a group $G$ of order 9. Suppose that $G$ is cyclic, then $G$ is abelian and there is nothing more to prove. Suppose that $G$ s not cyclic,then there exists an element $a$ of order 3 , and $A=\langle a\rangle$. Now $i_G(A)=3$, now $9 \nmid 3$ !, hence by the above result there is a normal subgroup $K$, non-trivial and $K \subseteq A$. But $|A|=3$, a prime order subgroup, hence has no non-trivial subgroup, so $K=A$. So $A$ is normal subgroup. Now since $G$ is not cyclic any non-identity element is of order 3.So Let $a(\neq$ $e) \in G$.Consider $A=\langle a\rangle$. As shown before $A$ is normal. $a$ commutes with any if its powers. Now Let $b \in G$ such that $b \notin A$. Then $b a b^{-1} \in A$ and hence $b a b^{-1}=a^i$.This implies $a=b^3 a b^{-3}=a^{i^3} \Longrightarrow a^{i^3-1}=e$. So, 3 divides $i^3-1$. Also by fermat's little theorem 3 divides $i^2-1$.So 3 divides $i-1$. But $0 \leq i \leq 2$. So $i=1$, is the only possibility and hence $a b=b a$. So $a \in Z(G)$ as $b$ was arbitrary. Since $a$ was arbitrary $G=Z(G)$. Hence $G$ is abelian.
-/

theorem Herstein_exercise_2_5_43 (G : Type*) [Group G] [Fintype G]
  (hG : card G = 9) :
  Nonempty (CommGroup G) := by
  classical
  -- Step 1: rewrite the hypothesis from `Fintype.card` to `Nat.card`
  --         because the prime-square lemma we will use expects `Nat.card`.
  have hNat : Nat.card G = 9 := by
    -- Step 1.1: `Nat.card` agrees with `Fintype.card` for finite types,
    --           so we simply rewrite using the standard equivalence.
    simpa [Nat.card_eq_fintype_card] using hG
  -- Step 2: express the numeric value `9` as the square of the prime `3`
  --         to match the required form `p ^ 2`.
  have hPow : Nat.card G = 3 ^ 2 := by
    -- Step 2.1: chain the previous equality with the arithmetic identity `9 = 3^2`.
    calc
      Nat.card G = 9 := hNat
      _ = 3 ^ 2 := by norm_num
  -- Step 3: provide the primality of `3` as a typeclass instance demanded by the lemma.
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  -- Step 4: invoke the mathlib classification result that any group of order `p^2`
  --         (here `3^2`) carries a commutative group structure.
  have hComm : CommGroup G :=
    IsPGroup.commGroupOfCardEqPrimeSq (p := 3) (G := G) hPow
  -- Step 5: package the constructed commutative structure into the expected `Nonempty` witness.
  exact ⟨hComm⟩


/-
The original formalization uses `Nonempty (CommGroup G)`, which only asserts
that the type G *admits some* commutative group structure. This structure could
be completely unrelated to the given `[Group G]` instance — for example, one
could transport `ZMod 9`'s commutative group structure via any bijection from
G to `ZMod 9` (which exists since `card G = 9`), without ever showing that
the given multiplication on G is commutative.

The informal statement "prove that a group of order 9 is abelian" asserts that
the *given* group operation is commutative, i.e., ∀ a b : G, a * b = b * a.

The corrected formalization directly states commutativity of the existing
group operation.
-/

theorem Herstein_exercise_2_5_43_corrected (G : Type*) [Group G] [Fintype G]
  (hG : card G = 9) :
  ∀ a b : G, a * b = b * a := by
  -- Step 1: Rewrite the cardinality hypothesis from `Fintype.card` to `Nat.card`.
  have hNat : Nat.card G = 9 := by
    simpa [Nat.card_eq_fintype_card] using hG
  -- Step 2: Express 9 as 3^2 to match the prime-square classification lemma.
  have hPow : Nat.card G = 3 ^ 2 := by
    calc Nat.card G = 9 := hNat
      _ = 3 ^ 2 := by norm_num
  -- Step 3: Provide the primality of 3 as a Fact instance.
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  -- Step 4: Invoke the Mathlib theorem that directly gives commutativity
  --   for any group of order p^2, stated as ∀ a b : G, a * b = b * a
  --   with respect to the existing [Group G] multiplication.
  exact IsPGroup.commutative_of_card_eq_prime_sq hPow
