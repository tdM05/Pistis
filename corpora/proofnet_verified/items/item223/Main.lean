import Mathlib
import Pistis
import items.item223.cyclic_lemmas
import items.item223.step1
import items.item223.step2
import items.item223.step3
import items.item223.step4
import items.item223.step5
import items.item223.step6
import items.item223.step7
import items.item223.step8
import items.item223.step9
import items.item223.step10
import items.item223.step11
import items.item223.step12
import items.item223.step13
import items.item223.step14
import items.item223.step15
import items.item223.step16
import items.item223.step17
set_option linter.unusedTactic false

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators
open Item223



/-Informal Statement

Show that if $G=\langle x\rangle$ is a cyclic group of order $n \geq 1$ then a subgroup $H$ is maximal if and only $H=\left\langle x^{p}\right\rangle$ for some prime $p$ dividing $n$.
-/

theorem Dummit_Foote_exercise_2_4_16c {n : ℕ+} {G : Type*} [Group G] {x : G}
  (hx : orderOf x = n) (hG : closure ({x} : Set G) = ⊤) (H : Subgroup G) :
  (∃ p : ℕ, Prime p ∧ p ∣ n ∧ H = Subgroup.closure {x ^ p}) ↔
  (H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤) := by
  pistis_intro "223.0"
    r"Show that if $G=\langle x\rangle$ is a cyclic group of order $n \geq 1$ then a subgroup $H$ is maximal if and only $H=\left\langle x^{p}\right\rangle$ for some prime $p$ dividing $n$."

  -- The iff splits into the forward arm `A → B` and the backward arm `B → A`.
  -- The NL proof's first part ("Suppose H is maximal [=B] … therefore H = ⟨x^p⟩ [=A]")
  -- proves the BACKWARD arm `B → A`; its converse proves the FORWARD arm `A → B`.
  -- The backward-arm segments (223.1–223.10) precede the converse segments (223.11–223.17)
  -- in the file, so we discharge the backward goal first with `case`.
  refine ⟨?fwd, ?bwd⟩

  case bwd =>
    -- B → A.  `hB` ("H is maximal") is in scope for every segment below.
    intro hB

    pistis_segment "223.1"
      r"Suppose $H$ is a maximal subgroup of $G$."
      (step1 : H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤) := by
        exact helper_Dummit_Foote_exercise_2_4_16c_step1 H hB

    pistis_assumption "223.2" r"$H$ is cyclic"
      (asm2_0 : ∃ g : G, H = Subgroup.closure {g}) := by
        exact helper_Dummit_Foote_exercise_2_4_16c_asm2 hx hG H
    pistis_segment "223.2"
      r"Then $H$ is cyclic, and we may write $H=\left\langle x^k\right\rangle$ for some integer $k$, with $k>1$."
      (step2 : ∃ k : ℕ, 1 < k ∧ k ∣ (n : ℕ) ∧ H = Subgroup.closure {x ^ k}) := by
        exact helper_Dummit_Foote_exercise_2_4_16c_step2 hx hG H hB asm2_0
    obtain ⟨k, hk1, hkn, hk2⟩ := step2

    pistis_segment "223.3"
      r"Let $d=(n, k)$."
      (step3 : ∃ d : ℕ, d = Nat.gcd (n : ℕ) k) := by
        exact helper_Dummit_Foote_exercise_2_4_16c_step3 (n : ℕ) k

    pistis_assumption "223.4" r"$H$ is a proper subgroup"
      (asm4_0 : H ≠ ⊤) := by exact hB.1
    pistis_segment "223.4"
      r"Since $H$ is a proper subgroup, we know by Proposition 6 that $d>1$."
      (step4 : 1 < Nat.gcd (n : ℕ) k) := by
        exact helper_Dummit_Foote_exercise_2_4_16c_step4 hx hG H k hk2 asm4_0
    obtain ⟨p, hp_prime, hp_dvd⟩ :=
      helper_Dummit_Foote_exercise_2_4_16c_step5 (n : ℕ) k step4

    pistis_segment "223.5"
      r"Choose a prime factor $p$ of $d$."
      (step5 : ∃ p : ℕ, Prime p ∧ p ∣ Nat.gcd (n : ℕ) k) := by
        exact ⟨p, hp_prime, hp_dvd⟩

    -- p ∣ k and p ∣ n (used in both case arms below).
    have hgcd_nk : Nat.gcd (n : ℕ) k = k := Nat.gcd_eq_right hkn
    have hpk : p ∣ k := by rw [hgcd_nk] at hp_dvd; exact hp_dvd
    have hpn : p ∣ (n : ℕ) := hp_dvd.trans (Nat.gcd_dvd_left _ _)

    -- Case split on whether `d = (n,k)` is prime, i.e. whether the prime factor `p` equals `k`.
    by_cases hcase : p = k
    · -- Case `k = p = d`: `d` is prime, so `H = ⟨x^k⟩` with `k = p` prime dividing `n`.
      pistis_assumption "223.6" r"$k=p=d$"
        (asm6_0 : k = p ∧ p = Nat.gcd (n : ℕ) k) := by
          refine ⟨hcase.symm, ?_⟩; rw [hgcd_nk]; exact hcase
      pistis_segment "223.6"
        r"If $k=p=d$ then $k \mid n$ as required.

If, however, $k$ is not prime, then consider the subgroup $K=\left\langle x^p\right\rangle$."
        (step6 : (k : ℕ) ∣ (n : ℕ)) := by
          exact helper_Dummit_Foote_exercise_2_4_16c_step6 (n : ℕ) k p asm6_0
      -- Conclude A: take the prime `p = k`.
      refine ⟨p, hp_prime, hpn, ?_⟩
      rw [hk2, hcase]
    · -- Case `k` not prime: the reductio `223.7`–`223.10` derives a contradiction.
      exfalso
      pistis_assumption "223.7" r"$p$ is a proper divisor of $k$"
        (asm7_0 : p ∣ k ∧ p ≠ k) := by exact ⟨hpk, hcase⟩
      pistis_segment "223.7"
        r"Since $p$ is a proper divisor of $k$, it follows that $H<K$."
        (step7 : H < Subgroup.closure {x ^ p}) := by
          exact helper_Dummit_Foote_exercise_2_4_16c_step7 hx H k p hk2 hkn hpn asm7_0

      pistis_assumption "223.8" r"$H$ is maximal"
        (asm8_0 : H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤) := by exact hB
      pistis_segment "223.8"
        r"But $H$ is maximal, so we must have $K=G$."
        (step8 : Subgroup.closure {x ^ p} = ⊤) := by
          exact helper_Dummit_Foote_exercise_2_4_16c_step8 H p step7 asm8_0

      pistis_segment "223.9"
        r"Again by Proposition 6 , we must then have $(p, n)=1$."
        (step9 : Nat.gcd p (n : ℕ) = 1) := by
          exact helper_Dummit_Foote_exercise_2_4_16c_step9 hx hG p step8

      pistis_assumption "223.10" r"$p$ divides $d$ which divides $n$"
        (asm10_0 : p ∣ Nat.gcd (n : ℕ) k ∧ Nat.gcd (n : ℕ) k ∣ (n : ℕ)) := by
          exact ⟨hp_dvd, Nat.gcd_dvd_left _ _⟩
      pistis_segment "223.10"
        r"However, $p$ divides $d$ which divides $n$, so $p \mid n$ and $(p, n)=p>1$, a contradiction."
        (step10 : False) := by
          exact helper_Dummit_Foote_exercise_2_4_16c_step10 (n : ℕ) k p hp_prime step9 asm10_0
      exact step10

  case fwd =>
    -- A → B.  `hA` ("H = ⟨x^p⟩ for a prime p dividing n") is in scope below.
    intro hA

    pistis_segment "223.11"
      r"Therefore $k=p$ and the left-to-right implication holds.
Now, for the converse, suppose $H=\left\langle x^p\right\rangle$ for $p$ a prime dividing $n$."
      (step11 : ∃ p : ℕ, Prime p ∧ p ∣ (n : ℕ) ∧ H = Subgroup.closure {x ^ p}) := by
        exact helper_Dummit_Foote_exercise_2_4_16c_step11 H hA
    obtain ⟨pc, hpc_prime, hpc_dvd, hHpc⟩ := step11

    -- `H ≠ ⊤` (since `gcd(n,pc) = pc ≠ 1`); needed to find a maximal `K ⊇ H`.
    have hHne : H ≠ ⊤ := by
      rw [hHpc]; intro htop
      have hg1 : Nat.gcd (orderOf x) pc = 1 := (closure_pow_eq_top_iff_gcd pc hG).mp htop
      rw [hx] at hg1
      have : pc ∣ Nat.gcd (n : ℕ) pc := Nat.dvd_gcd hpc_dvd (dvd_refl pc)
      rw [hg1] at this
      exact hpc_prime.ne_one (Nat.eq_one_of_dvd_one this)

    -- Reductio: suppose H is NOT maximal (¬B) and derive a contradiction.
    by_contra hnotB

    pistis_assumption "223.12" r"$H$ is not maximal"
      (asm12_0 : ¬(H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤)) := by exact hnotB
    pistis_segment "223.12"
      r"If $H$ is not maximal then the first part of this exercise shows that there is a maximal subgroup $K$ containing $H$."
      (step12 : ∃ K : Subgroup G, (K ≠ ⊤ ∧ ∀ L : Subgroup G, K ≤ L → L = K ∨ L = ⊤) ∧ H ≤ K) := by
        exact helper_Dummit_Foote_exercise_2_4_16c_step12 hx hG H hHne
    obtain ⟨K, hKmax, hHK⟩ := step12

    pistis_segment "223.13"
      r"Then $K=\left\langle x^q\right\rangle$."
      (step13 : ∃ q : ℕ, K = Subgroup.closure {x ^ q} ∧ Nat.gcd (n : ℕ) q = q) := by
        exact helper_Dummit_Foote_exercise_2_4_16c_step13 hx hG K
    obtain ⟨q, hKq, hqn⟩ := step13

    pistis_assumption "223.14" r"$x^p \in\left\langle x^q\right\rangle$"
      (asm14_0 : x ^ pc ∈ Subgroup.closure {x ^ q}) := by
        rw [← hKq]; apply hHK; rw [hHpc]; exact subset_closure (by simp)
    pistis_segment "223.14"
      r"So $x^p \in\left\langle x^q\right\rangle$, which implies $q \mid p$."
      (step14 : q ∣ pc) := by
        exact helper_Dummit_Foote_exercise_2_4_16c_step14 hx pc q hqn asm14_0

    pistis_segment "223.15"
      r"But the only divisors of $p$ are 1 and $p$."
      (step15 : ∀ m : ℕ, m ∣ pc → m = 1 ∨ m = pc) := by
        exact helper_Dummit_Foote_exercise_2_4_16c_step15 pc hpc_prime

    pistis_assumption "223.16" r"$q=1$"
      (asm16_0 : q = 1 → K = ⊤) := by
        intro hq1; rw [hKq, hq1, pow_one, hG]
    pistis_assumption "223.16" r"$q=p$"
      (asm16_1 : q = pc → H = K) := by
        intro hqp; rw [hHpc, hKq, hqp]
    pistis_segment "223.16"
      r"If $q=1$ then $K=G$ and $K$ cannot be a proper subgroup, and if $q=p$ then $H=K$ and $H$ cannot be a proper subgroup of $K$."
      (step16 : K = ⊤ ∨ H = K) := by
        exact helper_Dummit_Foote_exercise_2_4_16c_step16 H K q pc step14 step15 asm16_0 asm16_1

    pistis_assumption "223.17" r"This contradiction"
      (asm17_0 : K = ⊤ ∨ H = K) := by exact step16
    pistis_segment "223.17"
      r"This contradiction shows that $H$ is maximal."
      (step17 : H ≠ ⊤ ∧ ∀ K : Subgroup G, H ≤ K → K = H ∨ K = ⊤) := by
        exact helper_Dummit_Foote_exercise_2_4_16c_step17 H K hKmax hHne asm17_0
    exact hnotB step17
