import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Let $A$ be a normal subgroup of a group $G$, and suppose that $b \in G$ is an element of prime order $p$, and that $b \not\in A$. Show that $A \cap (b) = (e)$.
-/

/-Informal Proof

If $b \in G$ has order $p$, then $(b)$ is a cyclic group of order $p$. Since $A$ is a subgroup of $G$, we have $A \cap (b)$ is a subgroup of $G$. Also, $A \cap (b) \subseteq (b)$. So $A \cap (b)$ is a subgroup of $(b)$. Since $(b)$ is a cyclic group of order $p$, the only subgroups of $(b)$ are $(e)$ and $(b)$ itself.

Therefore, either $A \cap (b) = (e)$ or $A \cap (b) = (b)$. If $A \cap (b) = (e)$, then we are done. Otherwise, if $A \cap (b) = (b)$, then $A \subseteq (b)$. Since $A$ is a subgroup of $G$ and $A \subseteq (b)$, it follows that $A$ is a subgroup of $(b)$.

Since the only subgroups of $(b)$ are $(e)$ and $(b)$ itself, we have either $A = (e)$ or $A = (b)$. If $A = (e)$, then $A \cap (b) = (e)$ and we are done. But if $A = (b)$, then $b \in A$ as $b \in (b)$, which contradicts our hypothesis that $b \notin A$. So $A \neq (b)$.

Hence $A \cap (b) \neq (b)$. Therefore, $A \cap (b) = (e)$. This completes our proof.
-/

theorem Herstein_exercise_2_10_1 {G : Type*} [Group G] (A : Subgroup G)
  [A.Normal] {b : G} (hb : b ∉ A) (hp : Nat.Prime (orderOf b)) :
  A ⊓ (Subgroup.closure {b}) = ⊥ := by
  classical
  -- Step 1: Fix the prime order `p = orderOf b` and record the helper type-class instances.
  set p := orderOf b with hpdef
  -- Step 1.1: Transport the primality assumption to the new notation.
  have hp_prime : Nat.Prime p := by simpa [hpdef] using hp
  -- Step 1.2: Equip `ZMod p` with the customary prime-specific structure.
  haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
  haveI : NeZero p := ⟨hp_prime.ne_zero⟩
  -- Step 2: Prove that every element of the intersection already lies in the bottom subgroup.
  refine le_antisymm ?_ bot_le
  -- Step 2.1: Pick an arbitrary element and decompose its membership in the infimum.
  intro x hx
  rcases hx with ⟨hxA, hxClosure⟩
  -- Step 2.2: Translate the closure membership into the statement “`x` is a `ℤ`-power of `b`”.
  have hx_zpow : x ∈ Subgroup.zpowers b := by
    simpa [Subgroup.zpowers_eq_closure (g := b)] using hxClosure
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx_zpow
  -- Step 2.3: Reduce to showing `b ^ n = 1`, so that the element belongs to `⊥`.
  refine Subgroup.mem_bot.mpr ?_
  -- Step 2.4: Prove `b ^ n = 1` via a contradiction that would force `b ∈ A`.
  have hxpow_one : b ^ n = (1 : G) := by
    -- Step 2.4.1: Assume `b ^ n ≠ 1` and aim to contradict the hypothesis `b ∉ A`.
    by_contra hne
    -- Step 2.4.2: Show that the residue class of `n` in `ZMod p` is non-zero.
    have hk_ne_zero : (n : ZMod p) ≠ 0 := by
      intro hk
      have hdiv : (p : ℤ) ∣ n :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (a := n) (b := p)).1 hk
      obtain ⟨m, hm⟩ := hdiv
      have hpow : b ^ n = (1 : G) := by
        have hcalc :
            b ^ n = (b ^ (p : ℤ)) ^ m := by
          simp [hm, zpow_mul]
        have hcalc' :
            b ^ n = (b ^ p) ^ m := by
          simpa [hpdef, zpow_ofNat] using hcalc
        simpa [hpdef, pow_orderOf_eq_one b] using hcalc'
      exact hne hpow
    -- Step 2.4.3: Pick an integer representative of the inverse of `n` modulo `p`.
    obtain ⟨m, hm⟩ :=
      (ZMod.intCast_surjective (n := p)) ((n : ZMod p)⁻¹)
    -- Step 2.4.4: Convert the inverse relation into a divisibility statement over `ℤ`.
    have hdiv :
        (p : ℤ) ∣ n * m - 1 := by
      have :
          ((n * m - 1 : ℤ) : ZMod p) = 0 := by
        simp [Int.cast_mul, Int.cast_sub, Int.cast_one, hm, hk_ne_zero]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a := n * m - 1) (b := p)).1 this
    rcases hdiv with ⟨t, ht⟩
    -- Step 2.4.5: Rewrite `n * m` as `1 + p * t` to expose the key exponent.
    have hnm' : n * m = (p : ℤ) * t + 1 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, ht] using
        congrArg (fun z : ℤ => z + 1) ht
    have hnm :
        n * m = 1 + (p : ℤ) * t := by
      simpa [add_comm] using hnm'
    -- Step 2.4.6: Compute `(b ^ n) ^ m` explicitly and identify it with `b`.
    have hx_pow_eq :
        (b ^ n) ^ m = b := by
      have hnm_pow : b ^ (n * m) = b := by
        calc
          b ^ (n * m) = b ^ (1 + (p : ℤ) * t) := by simp [hnm]
          _ = b ^ 1 * b ^ ((p : ℤ) * t) := by
            simpa using (zpow_add b 1 ((p : ℤ) * t))
          _ = b * b ^ ((p : ℤ) * t) := by simp
          _ = b * (b ^ (p : ℤ)) ^ t := by
            simpa using congrArg (fun z => b * z) (zpow_mul b (p : ℤ) t)
          _ = b * (b ^ p) ^ t := by
            simp [hpdef]
          _ = b * 1 := by simp [hpdef, pow_orderOf_eq_one b]
          _ = b := by simp
      calc
        (b ^ n) ^ m = b ^ (n * m) := by
          simpa using (zpow_mul b n m).symm
        _ = b := hnm_pow
    -- Step 2.4.7: Use the subgroup property to deduce `b ∈ A`, contradicting `hb`.
    have hb_mem : b ∈ A := by
      have hx_pow_mem : (b ^ n) ^ m ∈ A := Subgroup.zpow_mem A hxA m
      simpa [hx_pow_eq] using hx_pow_mem
    exact hb hb_mem
  -- Step 2.5: Conclude that the element lies in `⊥`, completing the inequality.
  simpa using hxpow_one
