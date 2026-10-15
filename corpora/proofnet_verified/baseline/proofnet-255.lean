import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $G$ is a finite group of even order, show that there must be an element $a \neq e$ such that $a=a^{-1}$.
-/

/-Informal Proof

First note that $a=a^{-1}$ is the same as saying $a^2=e$, where $e$ is the identity. I.e. the statement is that there exists at least one element of order 2 in $G$.
Every element $a$ of $G$ of order at least 3 has an inverse $a^{-1}$ that is not itself -- that is, $a \neq a^{-1}$. So the subset of all such elements has an even cardinality (/size). There's exactly one element with order 1 : the identity $e^1=e$. So $G$ contains an even number of elements -call it $2 k$-- of which an even number are elements of order 3 or above -- call that $2 n$ where $n<k$-- and exactly one element of order 1 . Hence the number of elements of order 2 is
$$
2 k-2 n-1=2(k-n)-1
$$
This cannot equal 0 as $2(k-n)$ is even and 1 is odd. Hence there's at least one element of order 2 in $G$, which concludes the proof.
-/

theorem Herstein_exercise_2_1_18 {G : Type*} [Group G]
  [Fintype G] (hG2 : Even (card G)) :
  ∃ (a : G), a ≠ 1 ∧ a = a⁻¹ := by
  classical
  -- Step 1: Unpack the even-cardinality hypothesis to obtain an explicit witness for `2 ∣ |G|`.
  obtain ⟨k, hk⟩ := hG2
  -- Step 1.1: Turn the witness equality `|G| = k + k` into the standard divisibility form.
  have h_two_dvd : 2 ∣ Fintype.card G := by
    -- Step 1.1.1: Rewrite `k + k` as `2 * k` so that the divisibility condition follows immediately.
    refine ⟨k, ?_⟩
    simpa [two_mul] using hk
  -- Step 2: Record that `2` is prime, a prerequisite for applying Cauchy's theorem.
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Step 3: Apply Cauchy's theorem to obtain an element whose order is exactly `2`.
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := G) (p := 2) h_two_dvd
  -- Step 4: Show that this element is nontrivial; an element of order `2` cannot be the identity.
  have hx_ne_one : x ≠ (1 : G) := by
    -- Step 4.1: Since `orderOf x = 2`, it is automatically different from `1`.
    have hx_order_ne_one : orderOf x ≠ 1 := by
      intro hx_order
      -- Step 4.1.1: Rewrite `orderOf x` as `2` in the assumption to obtain a contradiction.
      have hx_contra := hx
      rw [hx_order] at hx_contra
      exact (Nat.succ_ne_self 1) hx_contra.symm
    -- Step 4.2: If `x` were the identity, its order would be `1`, contradicting Step 4.1.
    intro hx1
    exact hx_order_ne_one (orderOf_eq_one_iff.mpr hx1)
  -- Step 5: Convert the order information into the self-inverse property `x = x⁻¹`.
  have hx_sq : x ^ 2 = (1 : G) := by
    -- Step 5.1: `x ^ orderOf x = 1` for any element; insert `orderOf x = 2`.
    simpa [hx] using pow_orderOf_eq_one x
  -- Step 5.2: Rewrite `x ^ 2 = 1` as `x * x = 1` and cancel to prove `x = x⁻¹`.
  have hx_inv : x = x⁻¹ := by
    -- Step 5.2.1: Translate the square identity into a multiplicative one.
    have hx_mul : x * x = (1 : G) := by simpa [pow_two] using hx_sq
    -- Step 5.2.2: Multiply both sides on the right by `x⁻¹` to isolate `x`.
    have hx_cancelled := congrArg (fun y : G => y * x⁻¹) hx_mul
    -- Step 5.2.3: Simplify both sides to reach the desired equality by cancelling the extra factor.
    have hx_simplified := hx_cancelled
    simp [mul_assoc] at hx_simplified
    exact hx_simplified
  -- Step 6: Package the nontrivial element together with the self-inverse property.
  exact ⟨x, hx_ne_one, hx_inv⟩
