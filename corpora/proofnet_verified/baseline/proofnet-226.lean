import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Use Lagrange's Theorem in the multiplicative group $(\mathbb{Z} / p \mathbb{Z})^{\times}$to prove Fermat's Little Theorem: if $p$ is a prime then $a^{p} \equiv a(\bmod p)$ for all $a \in \mathbb{Z}$.
-/

/-Informal Proof

Solution: If $p$ is prime, then $\varphi(p)=p-1$ (where $\varphi$ denotes the Euler totient). Thus
$$
\mid\left((\mathbb{Z} /(p))^{\times} \mid=p-1 .\right.
$$
So for all $a \in(\mathbb{Z} /(p))^{\times}$, we have $|a|$ divides $p-1$. Hence
$$
a=1 \cdot a=a^{p-1} a=a^p \quad(\bmod p) .
$$
-/

theorem Dummit_Foote_exercise_3_2_16 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p] := by
  /-
  **Goal**: Prove Fermat's Little Theorem for integers: a^p ≡ a (mod p) for prime p.

  **Proof Strategy**:
  We use the fact that in ZMod p (integers modulo p), for any element x,
  we have x^p = x (this is ZMod.pow_card from Mathlib).

  Then we translate equality in ZMod p back to integer congruence using
  the lemma ZMod.intCast_eq_intCast_iff: (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c].
  -/

  -- Step 1: We need to establish that p is prime as a Fact instance
  -- so that ZMod.pow_card can be applied
  haveI : Fact (Nat.Prime p) := ⟨hp⟩

  -- Step 2: Use the characterization that integer congruence is equivalent to
  -- equality when cast to ZMod p.
  -- By ZMod.intCast_eq_intCast_iff: (a^p : ZMod p) = (a : ZMod p) ↔ a^p ≡ a [ZMOD p]
  rw [← ZMod.intCast_eq_intCast_iff]

  -- Step 3: Now we need to show (a^p : ZMod p) = (a : ZMod p)
  -- Step 3.1: Push the cast inside the power
  push_cast

  -- Step 4: Apply Fermat's Little Theorem in ZMod p
  -- ZMod.pow_card states: x^p = x for any x : ZMod p when p is prime
  exact ZMod.pow_card (a : ZMod p)
