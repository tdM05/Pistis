import Mathlib

open Real
open scoped BigOperators
open scoped NumberTheorySymbols



/-Informal Statement

Show that if $a$ is negative then $p \equiv q(4 a)$ together with $p\not | a$ imply $(a / p)=(a / q)$.
-/

/-Informal Proof

\newcommand{\legendre}[2]{\genfrac{(}{)}{}{}{#1}{#2}}
Write $a = -A, A>0$. As $p \equiv q \pmod {4a}$, we know from Prop. 5.3.3. (b) that $(A/p) = (A/q)$.

Moreover,
\begin{align*}
\legendre{a}{p}&= \legendre{-A}{p} = (-1)^{(p-1)/2} \legendre{A}{p}\\
\legendre{a}{q}&= \legendre{-A}{q} = (-1^{(q-1)/2} \legendre{A}{q}
\end{align*}
As  $p \equiv q \pmod {4a}$, $ p = q + 4ak, k\in \mathbb{Z}$, so
$$(-1)^{(p-1)/2} = (-1)^{(q+4ak-1)/2} = (-1)^{(q-1)/2},$$
so $(a/p) = (a/q)$.
-/

theorem Ireland_Rosen_exercise_5_37 {p q : ℕ} [Fact (p.Prime)] [Fact (q.Prime)] {a : ℤ}
  (ha : a < 0) (h0 : p ≡ q [ZMOD 4*a]) (h1 : ¬ ((p : ℤ) ∣ a)) :
  legendreSym p a = legendreSym q a := by
  classical
  -- Step 1: Extract the primality assumptions for `p` and `q`.
  have hp' : p.Prime := (inferInstance : Fact (p.Prime)).out
  -- Step 1.1: Record the primality of `q`.
  have hq' : q.Prime := (inferInstance : Fact (q.Prime)).out
  -- Step 2: Split into the special case where `p = 2` and the generic case.
  by_cases hp2 : p = 2
  · -- Step 2.1: Assume `p = 2` and reduce the congruence modulo `2` to compare parities.
    have h_mod_two : (p : ℤ) ≡ q [ZMOD (2 : ℤ)] := by
      -- Step 2.1.1: Witness that `2` divides the modulus `4 * a`.
      have h_two_dvd : (2 : ℤ) ∣ 4 * a := by
        -- Step 2.1.1.1: Provide the explicit multiple exhibiting the divisibility.
        refine ⟨2 * a, ?_⟩
        -- Step 2.1.1.2: Verify the arithmetic identity `2 * (2 * a) = 4 * a`.
        ring
      -- Step 2.1.2: Apply divisibility reduction to pass from modulus `4 * a` to `2`.
      exact Int.ModEq.of_dvd h_two_dvd h0
    -- Step 2.2: Translate the parity relation back to natural numbers.
    have h_mod_two_nat : q ≡ p [MOD 2] := by
      -- Step 2.2.1: Symmetrize the congruence so that `Nat` conversion matches the expected order.
      have h_symm := h_mod_two.symm
      -- Step 2.2.2: Use the integer-to-natural congruence correspondence.
      simpa using (Int.natCast_modEq_iff).mp h_symm
    -- Step 2.3: Combine the parity relation with `p = 2` to deduce `q ≡ 0 (mod 2)`.
    have h_q_zero : q ≡ 0 [MOD 2] := by
      -- Step 2.3.1: Record the trivial congruence `2 ≡ 0 (mod 2)`.
      have h_p_zero : p ≡ 0 [MOD 2] := by
        -- Step 2.3.1.1: Simplify the remainders explicitly.
        simp [Nat.ModEq, hp2]
      -- Step 2.3.2: Transitively combine `q ≡ p` with `p ≡ 0`.
      exact h_mod_two_nat.trans h_p_zero
    -- Step 2.4: Convert this congruence to divisibility information.
    have h_two_dvd_q : 2 ∣ q := (Nat.modEq_zero_iff_dvd).1 h_q_zero
    -- Step 2.5: Use the primality of `q` to deduce that `q = 2`.
    have hq2 : q = 2 :=
      (hq'.dvd_iff_eq (a := 2) (by decide : (2 : ℕ) ≠ 1)).mp h_two_dvd_q
    -- Step 2.6: Rewrite the goal with the identified primes.
    subst hp2
    subst hq2
    -- Step 2.7: The equality now holds by reflexivity.
    rfl
  · -- Step 3: Work under the assumption that `p ≠ 2`, so both primes are odd.
    have hp_odd : Odd p := (hp'.eq_two_or_odd').resolve_left hp2
    -- Step 3.1: Reduce the congruence modulo `2` to transport parity information.
    have h_mod_two : (p : ℤ) ≡ q [ZMOD (2 : ℤ)] := by
      -- Step 3.1.1: Exhibit the divisibility `2 ∣ 4 * a` as before.
      have h_two_dvd : (2 : ℤ) ∣ 4 * a := by
        -- Step 3.1.1.1: Provide the explicit multiple for the divisibility.
        refine ⟨2 * a, ?_⟩
        -- Step 3.1.1.2: Verify the multiplication identity.
        ring
      -- Step 3.1.2: Apply the reduction to the original congruence.
      exact Int.ModEq.of_dvd h_two_dvd h0
    -- Step 3.2: Convert the parity congruence to the natural-number setting.
    have h_mod_nat : p ≡ q [MOD 2] := (Int.natCast_modEq_iff).mp h_mod_two
    -- Step 3.3: Use the parity equality to show that `q ≠ 2`.
    have h_mod_eq : p % 2 = q % 2 := by
      -- Step 3.3.1: Unfold the definition of `Nat.ModEq`.
      simpa [Nat.ModEq] using h_mod_nat
    -- Step 3.3.2: Compute the remainder of `p` modulo `2` using its oddness.
    have hp_mod_one : p % 2 = 1 := by
      -- Step 3.3.2.1: Expand the oddness witness.
      rcases hp_odd with ⟨kp, hkp⟩
      -- Step 3.3.2.2: Evaluate the modulus via direct simplification.
      simp [hkp]
    -- Step 3.3.3: Transfer the remainder equality to `q`.
    have hq_mod_one : q % 2 = 1 := by
      -- Step 3.3.3.1: Substitute the computed value for `p % 2`.
      have h_mod_eq' := h_mod_eq.symm
      -- Step 3.3.3.2: Simplify the equality to isolate `q % 2`.
      simp [hp_mod_one] at h_mod_eq'
      exact h_mod_eq'
    -- Step 3.3.4: Show that `q` cannot equal `2`.
    have hq_ne_two : q ≠ 2 := by
      -- Step 3.3.4.1: Assume `q = 2` and reach a contradiction on remainders.
      intro hq2
      -- Step 3.3.4.1.1: Simplify the remainder equality using `q = 2`.
      simp [hq2] at hq_mod_one
    -- Step 3.4: Conclude that `q` is odd as well.
    have hq_odd : Odd q := (hq'.eq_two_or_odd').resolve_left hq_ne_two
    -- Step 3.5: Reinterpret the original congruence with modulus `4 * a.natAbs`.
    have ha_nonpos : a ≤ 0 := le_of_lt ha
    -- Step 3.5.1: Express `a.natAbs` in terms of `a` using the negativity hypothesis.
    have ha_abs : ((a.natAbs : ℕ) : ℤ) = -a :=
      Int.ofNat_natAbs_of_nonpos ha_nonpos
    -- Step 3.5.2: Identify the positive modulus corresponding to `4 * a`.
    have h_modulus :
        ((4 * a.natAbs : ℕ) : ℤ) = -(4 * a) := by
      -- Step 3.5.2.1: Pull out the factor `4` at the level of integers.
      calc
        ((4 * a.natAbs : ℕ) : ℤ)
            = (4 : ℤ) * ((a.natAbs : ℕ) : ℤ) := by simp [Nat.cast_mul]
        _ = (4 : ℤ) * (-a) := by simp [ha_abs]
        _ = -(4 * a) := by ring
    -- Step 3.5.3: Transfer divisibility from `4 * a` to `4 * a.natAbs`.
    have h_diff_dvd : (4 * a) ∣ (q : ℤ) - p := (Int.modEq_iff_dvd).1 h0
    -- Step 3.5.4: Convert the divisibility using the sign change.
    have h_mod_natAbs_int :
        (p : ℤ) ≡ q [ZMOD (4 * a.natAbs)] := by
      -- Step 3.5.4.1: Extract an explicit witness for the original divisibility.
      obtain ⟨k, hk⟩ := h_diff_dvd
      -- Step 3.5.4.2: Supply the adjusted witness for the positive modulus.
      refine (Int.modEq_iff_dvd).2 ?_
      refine ⟨-k, ?_⟩
      -- Step 3.5.4.3: Simplify using the identity between the moduli.
      calc
        (q : ℤ) - p
            = (4 * a) * k := hk
        _ = (-(4 * a)) * (-k) := by simp
        _ = ((4 * a.natAbs : ℕ) : ℤ) * (-k) := by simp [h_modulus]
    -- Step 3.5.5: Return to natural-number congruences for the enlarged modulus.
    have h_mod_natAbs : p ≡ q [MOD 4 * a.natAbs] :=
      (Int.natCast_modEq_iff).mp h_mod_natAbs_int
    -- Step 3.6: Record the equality of remainders modulo `4 * a.natAbs`.
    have h_mod_natAbs_eq :
        p % (4 * a.natAbs) = q % (4 * a.natAbs) := by
      simpa [Nat.ModEq] using h_mod_natAbs
    -- Step 3.7: Apply the modulus-reduction property of the Jacobi symbol to `p`.
    have hJ_p_mod :
        J(a | p) = J(a | p % (4 * a.natAbs)) := jacobiSym.mod_right a hp_odd
    -- Step 3.8: Apply the same reduction to `q`.
    have hJ_q_mod :
        J(a | q) = J(a | q % (4 * a.natAbs)) := jacobiSym.mod_right a hq_odd
    -- Step 3.9: Use the equality of remainders to identify the reduced symbols.
    have h_remainder :
        J(a | p % (4 * a.natAbs)) = J(a | q % (4 * a.natAbs)) := by
      -- Step 3.9.1: Map the remainder equality through the function `t ↦ J(a | t)`.
      simpa using congrArg (fun t => J(a | t)) h_mod_natAbs_eq
    -- Step 3.10: Chain all equalities back to the original Legendre symbols.
    calc
      legendreSym p a
          = J(a | p) := jacobiSym.legendreSym.to_jacobiSym p a
      _ = J(a | p % (4 * a.natAbs)) := hJ_p_mod
      _ = J(a | q % (4 * a.natAbs)) := h_remainder
      _ = J(a | q) := hJ_q_mod.symm
      _ = legendreSym q a := (jacobiSym.legendreSym.to_jacobiSym q a).symm
