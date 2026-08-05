import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $G$ is an abelian group of order $p q$, where $p$ and $q$ are distinct primes, then $G$ is cyclic.
-/

/-Informal Proof

Let $G$ be an abelian group of order $p q$. We need to prove that if $p$ and $q$ are distinct primes than $G$ is cyclic. By Cauchy's theorem there are $a, b \in G$ with $a$ of order $p$ and $b$ of order $q$. Since $(|a|,|b|)=1$ and $a b=b a$ then $|a b|=|a| \cdot|b|=p q$. Therefore $a b$ is an element of order $p q$, the order of $G$, which means $G$ is cyclic.
-/

theorem Dummit_Foote_exercise_4_4_2 {G : Type*} [Fintype G] [CommGroup G]
  {p q : Nat.Primes} (hpq : p ≠ q) (hG : card G = p*q) :
  IsCyclic G := by
  classical
  -- Step 1: Re-express the cardinality information and register prime facts for `p` and `q`.
  have hcard_nat : Nat.card G = (p : ℕ) * (q : ℕ) := by
    -- Step 1.1: Convert the `Fintype` cardinality to `Nat.card` so that later lemmas can use it.
    simpa [Nat.card_eq_fintype_card] using hG
  -- Step 1.2: Upgrade the primality proofs to `Fact` instances required by Cauchy's theorem.
  haveI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
  haveI : Fact (Nat.Prime (q : ℕ)) := ⟨q.2⟩
  -- Step 2: Verify that each prime divisor of `|G|` actually divides `card G`, preparing Cauchy.
  have hp_dvd_card : (p : ℕ) ∣ Fintype.card G := by
    -- Step 2.1: Use the equality `|G| = p * q` to witness the divisibility by `p` directly.
    refine hG ▸ ?_
    exact dvd_mul_of_dvd_left (dvd_rfl : (p : ℕ) ∣ (p : ℕ)) _
  have hq_dvd_card : (q : ℕ) ∣ Fintype.card G := by
    -- Step 2.2: Symmetrically obtain the divisibility by `q`.
    refine hG ▸ ?_
    exact dvd_mul_of_dvd_right (dvd_rfl : (q : ℕ) ∣ (q : ℕ)) _
  -- Step 3: Invoke Cauchy's theorem twice to find elements of orders `p` and `q`.
  obtain ⟨a, ha⟩ :=
    exists_prime_orderOf_dvd_card (G := G) (p := (p : ℕ)) hp_dvd_card
  obtain ⟨b, hb⟩ :=
    exists_prime_orderOf_dvd_card (G := G) (p := (q : ℕ)) hq_dvd_card
  -- Step 4: Record commutativity and the coprimality of the two prime orders.
  have hcomm : Commute a b := by
    -- Step 4.1: Every pair of elements commutes in an abelian group.
    simpa using (Commute.all a b)
  have hp_ne_hq : (p : ℕ) ≠ (q : ℕ) := by
    -- Step 4.2: Different primes remain different after forgetting proofs.
    intro h
    apply hpq
    apply Subtype.ext
    simpa using h
  have h_not_dvd : ¬(p : ℕ) ∣ (q : ℕ) := by
    -- Step 4.3: If `p` divided `q`, primality would force `p = q`, contradicting `hpq`.
    intro hdiv
    rcases (Nat.dvd_prime q.2).1 hdiv with hcase | hcase
    · exact p.2.ne_one hcase
    · exact hp_ne_hq hcase
  have hcop_nat : Nat.Coprime (p : ℕ) (q : ℕ) :=
    -- Step 4.4: Translate the non-divisibility into numerical coprimality.
    (p.2.coprime_iff_not_dvd).2 h_not_dvd
  have hcop_orders : (orderOf a).Coprime (orderOf b) := by
    -- Step 4.5: Transport coprimality from the primes to the actual orders extracted above.
    simpa [ha, hb] using hcop_nat
  -- Step 5: Compute the order of the product using the coprime-order lemma for commuting elements.
  have horder_mul : orderOf (a * b) = orderOf a * orderOf b := by
    -- Step 5.1: Apply `orderOf_mul_eq_mul_orderOf_of_coprime` with the gathered data.
    simpa using hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop_orders
  have horder_pq : orderOf (a * b) = (p : ℕ) * (q : ℕ) := by
    -- Step 5.2: Rewrite the abstract orders back in terms of the primes `p` and `q`.
    simpa [ha, hb, Nat.mul_comm] using horder_mul
  -- Step 6: Identify this order with the actual size of `G` to prepare for the cyclicity criterion.
  have horder_card : orderOf (a * b) = Fintype.card G := by
    -- Step 6.1: Use the given cardinality equality to match both sides.
    simpa [hG, Nat.mul_comm] using horder_pq
  have horder_natcard : orderOf (a * b) = Nat.card G := by
    -- Step 6.2: Switch from `Fintype.card` to `Nat.card` for compatibility with the standard lemma.
    simpa [Nat.card_eq_fintype_card] using horder_card
  -- Step 7: Apply the characterization of cyclic finite groups via an element of maximal order.
  exact isCyclic_of_orderOf_eq_card (a * b) horder_natcard
