import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Prove that there are infinitely many primes congruent to $-1$ (modulo $4$).
-/

/-Informal Proof

First we show a lemma: if $a \equiv 3(\bmod 4)$ then there exists a prime $p$ such that $p \mid a$ and $p \equiv 3(\bmod 4)$.

    Clearly, all primes dividing $a$ are odd. Suppose all of them would be $\equiv 1(\bmod 4)$. Then their product would also be $a \equiv 1(\bmod 4)$, which is a contradiction.

To prove the main claim, suppose that $p_1, \ldots, p_n$ would be all such primes. (In particular, we have $p_1=3$.) Consider $a=4 p_2 \cdots p_n+3$. (Or you can take $a=4 p_2 \cdots p_n-1$.) Show that $p_i \nmid a$ for $i=1, \ldots, n$. (The case $3 \nmid a$ is solved differently than the other primes - this is the reason for omitting $p_1$ in the definition of $a$.) Then use the above lemma to get a contradiction.
-/

theorem Artin_exercise_11_13_3 (N : ℕ):
  ∃ p ≥ N, Nat.Prime p ∧ p + 1 ≡ 0 [MOD 4] := by
  classical
  -- Step 1: provide a `NeZero` instance for 4 so arithmetic in `ZMod 4` works smoothly.
  haveI : NeZero (4 : ℕ) := ⟨by decide⟩
  -- Step 2: note that −1 is a unit in `ZMod 4`, enabling Dirichlet's theorem in that residue class.
  have hUnit : IsUnit ((-1 : ZMod 4)) :=
    -- Step 2.1: take the negation of the unit `1` in `ZMod 4`.
    (IsUnit.neg (show IsUnit (1 : ZMod 4) from isUnit_one))
  -- Step 3: apply Dirichlet's theorem to obtain a prime `p > N` with `(p : ZMod 4) = -1`.
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 4) (a := (-1 : ZMod 4)) hUnit N
  -- Step 4: convert the strict inequality `p > N` into the requested weak inequality `p ≥ N`.
  have hp_ge : p ≥ N := le_of_lt hp_gt
  -- Step 5: rewrite the congruence into a statement about the cast of `p + 1` inside `ZMod 4`.
  have hp_cast : ((p + 1 : ℕ) : ZMod 4) = 0 := by
    -- Step 5.1: expand the cast and use the congruence `(p : ZMod 4) = -1`.
    simp [Nat.cast_add, hp_mod]
  -- Step 6: turn the vanishing of the cast into a divisibility statement in the natural numbers.
  have hdiv : (4 : ℕ) ∣ p + 1 :=
    -- Step 6.1: convert the `ZMod` equality into plain divisibility.
    (ZMod.natCast_eq_zero_iff (p + 1) 4).1 hp_cast
  -- Step 7: express the divisibility as the desired congruence `p + 1 ≡ 0 [MOD 4]`.
  have hp_modeq : p + 1 ≡ 0 [MOD 4] := (Nat.modEq_zero_iff_dvd).2 hdiv
  -- Step 8: assemble the witnesses satisfying the existential statement.
  exact ⟨p, hp_ge, hp_prime, hp_modeq⟩
