import Mathlib

open Real
open scoped BigOperators



/-Informal Statement

Show that there are infinitely many primes congruent to $-1$ modulo 6 .
-/

/-Informal Proof

Let $n$ any integer such that $n\geq 3$, and $N = n! -1 =   2 \times 3 \times\cdots\times n - 1 >1$. 

Then $N \equiv -1 \pmod 6$. As $6k +2, 6k +3, 6k +4$ are composite for all integers $k$, every prime factor of $N$ is congruent to $1$ or $-1$ modulo $6$.  If every prime factor of $N$ was congruent to 1, then $N \equiv 1 \pmod 6$ : this is a contradiction because $-1 \not \equiv 1 \pmod 6$.  So there exists a prime factor $p$ of $N$ such that $p\equiv -1 \pmod 6$.

If $p\leq n$, then $p \mid n!$, and $p \mid N = n!-1$, so $p \mid 1$. As $p$ is prime, this is a contradiction, so $p>n$. 

Conclusion :

 for any integer $n$, there exists a prime $p >n$ such that $p \equiv -1 \pmod 6$ : there are infinitely many primes congruent to $-1$ modulo $6$.
-/

theorem Ireland_Rosen_exercise_3_1 : Infinite {p : Nat.Primes // p ≡ -1 [ZMOD 6]} := by
  -- Step 1: certify that the residue class `-1 (mod 6)` is admissible (coprime to 6).
  have h_coprime : IsCoprime (-1 : ℤ) 6 := by
    -- Step 1.1: exhibit integers `u = -1`, `v = 0` with the Bézout identity `u * (-1) + v * 6 = 1`.
    refine ⟨-1, 0, ?_⟩
    -- Step 1.2: simplify `(-1) * (-1) + 0 * 6` to `1`, confirming coprimality.
    ring

  -- Step 2: Dirichlet's theorem gives, for every bound `n`, a prime `p > n` with `p ≡ -1 [ZMOD 6]`.
  have h_exists :
      ∀ n : ℕ, ∃ p > n, p.Prime ∧ (p : ℤ) ≡ (-1 : ℤ) [ZMOD 6] := by
    -- Step 2.1: specialize `Nat.forall_exists_prime_gt_and_modEq` to modulus `6` and residue `-1`.
    intro n
    simpa using
      Nat.forall_exists_prime_gt_and_zmodEq n (q := 6) (a := (-1 : ℤ)) (by norm_num) h_coprime

  -- Step 3: package the desired primes into a set `S` of natural numbers.
  let S : Set ℕ := {p : ℕ | p.Prime ∧ (p : ℤ) ≡ (-1 : ℤ) [ZMOD 6]}
  -- Step 3.1: show `S` is unbounded above—every `n` is beaten by some `p ∈ S`.
  have h_unbounded : ∀ n : ℕ, ∃ p ∈ S, n < p := by
    intro n
    -- Step 3.1.1: obtain the Dirichlet prime `p` promised for the bound `n`.
    obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ := h_exists n
    -- Step 3.1.2: record that this `p` lies in `S` and exceeds `n`.
    refine ⟨p, ?_, hp_gt⟩
    exact ⟨hp_prime, hp_mod⟩

  -- Step 4: turn unboundedness of `S` into infinitude of `S` as a set.
  have h_inf_set : S.Infinite :=
    -- Step 4.1: apply the general lemma that an unbounded set in a preorder is infinite.
    Set.infinite_of_forall_exists_gt (α := ℕ) (s := S) h_unbounded

  -- Step 5: rephrase set-level infinitude as infinitude of the corresponding subtype of `ℕ`.
  have h_inf_subtype :
      Infinite {p : ℕ // p.Prime ∧ (p : ℤ) ≡ (-1 : ℤ) [ZMOD 6]} :=
    Set.infinite_coe_iff.mpr h_inf_set
  -- Step 5.1: register the previous result as an instance for the domain of the embedding below.
  haveI : Infinite {p : ℕ // p.Prime ∧ (p : ℤ) ≡ (-1 : ℤ) [ZMOD 6]} := h_inf_subtype

  -- Step 6: build an explicit injective embedding into the target subtype over `Nat.Primes`.
  let embed :
      {p : ℕ // p.Prime ∧ (p : ℤ) ≡ (-1 : ℤ) [ZMOD 6]} →
        {p : Nat.Primes // p ≡ (-1 : ℤ) [ZMOD 6]} :=
    fun p =>
      -- Step 6.1: wrap the natural prime as an element of `Nat.Primes`, carrying over the congruence proof.
      ⟨⟨p.1, p.2.1⟩, by simpa using p.2.2⟩

  -- Step 6.2: verify that `embed` is injective, so it preserves infinitude.
  have h_embed_injective : Function.Injective embed := by
    intro x y hxy
    -- Step 6.2.1: equal images give equal underlying natural numbers after unfolding the embedding.
    have h_nat : x.1 = y.1 := by
      -- Step 6.2.1.1: compare the first component (a prime) and then project to `ℕ`.
      have h_val := congrArg (fun q => (q.1 : ℕ)) hxy
      -- Step 6.2.1.2: unfold `embed` so the equality simplifies to the carriers.
      dsimp [embed] at h_val
      simpa using h_val
    -- Step 6.2.2: conclude the subtypes coincide by extensionality on the carrier.
    apply Subtype.ext
    exact h_nat

  -- Step 7: transport infinitude through the injective embedding to finish the proof.
  exact Infinite.of_injective embed h_embed_injective
