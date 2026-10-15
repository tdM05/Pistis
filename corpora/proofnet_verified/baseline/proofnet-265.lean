import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Prove that if $p > q$ are two primes such that $q \mid p - 1$, then any two nonabelian groups of order $pq$ are isomorphic.
-/

/-Informal Proof

For a nonabelian group of order $p q$, the structure of the group $G$ is set by determining the relation $a b a^{-1}=b^{k^{\frac{p-1}{q}}}$ for some generator $k$ of the cyclic group. Here we are using the fact that $k^{\frac{p-1}{q}}$ is a generator for the unique subgroup of order $q$ in $U_p$ (a cyclic group of order $m$ has a unique subgroup of order $d$ for each divisor $d$ of $m$ ). The other possible generators of this subgroup are $k^{\frac{l(p-1)}{q}}$ for each $1 \leq l \leq q-1$, so these give potentially new group structures. Let $G^{\prime}$ be a group with an element $c$ of order $q$, an element $d$ of order $p$ with structure defined by the relation $c d c^{-1}=d^{k^{\frac{l(p-1)}{q}}}$. We may then define
$$
\begin{aligned}
\phi: G^{\prime} & \rightarrow G \\
c & \mapsto a^l \\
d & \mapsto b
\end{aligned}
$$
since $c$ and $a^l$ have the same order and $b$ and $d$ have the same order this is a well defined function.
Since
$$
\begin{aligned}
\phi(c) \phi(d) \phi(c)^{-1} & =a^l b a^{-l} \\
& =b^{\left(k^{\frac{p-1}{q}}\right)^l} \\
& =b^{k^{\frac{l(p-1)}{q}}} \\
& =\phi(d)^{k^{\frac{l(p-1)}{q}}}
\end{aligned}
$$
$\phi\left(c^i d^j\right)=a^{l i} b^j=e$ only if $i=j=0$, so $\phi$ is 1-to-l. Therefore $G$ and $G^{\prime}$ are isomorphic and so up to isomorphism there is only one nonabelian group of order $p q$.
-/

/-
  High-level proof strategy:

  This is a deep classification theorem from group theory: all nonabelian groups of order pq
  (with p > q primes and q | p-1) are isomorphic.

  The proof requires:
  1. Showing both G and H have structure as semidirect products P ⋊ Q
  2. Showing the semidirect product structures are isomorphic

  Key mathematical facts:
  - By Sylow theorems, the Sylow p-subgroup P is unique and normal
  - By Schur-Zassenhaus, there exists a complement Q (a Sylow q-subgroup)
  - G ≅ P ⋊_φ Q for some nontrivial action φ: Q → Aut(P)
  - Since Aut(P) ≅ Z_{p-1} has a unique subgroup of order q, all nontrivial
    semidirect products with this structure are isomorphic

  The formal proof uses the semidirect product classification approach.
-/

theorem Herstein_exercise_2_8_15 {G H: Type*} [Fintype G] [Group G] [Fintype H] [Group H]
  (hG_nonab : ∃ x y : G, x * y ≠ y * x) (hH_nonab : ∃ x y : H, x * y ≠ y * x)
  {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
  (h : p > q) (h1 : q ∣ p - 1) (hG : card G = p*q) (hH : card H = p*q) :
  Nonempty (G ≃* H) := by
  classical
  /-
    Step 1: Establish basic facts about p and q.
    p > q are primes with q | p-1, so p ≠ q and gcd(p,q) = 1.
  -/
  -- Step 1.1: p ≠ q (since p > q)
  have hpq_ne : p ≠ q := ne_of_gt h
  -- Step 1.2: gcd(p, q) = 1
  have hpq_coprime : Nat.Coprime p q := Nat.coprime_primes hp hq |>.mpr hpq_ne

  /-
    Step 2: Set up Sylow theory.
    Since |G| = pq with p > q primes, the Sylow p-subgroup is unique and normal.
  -/
  -- Step 2.1: Register prime facts as instances
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (Nat.Prime q) := ⟨hq⟩

  -- Step 2.2: The Sylow p-subgroups
  let P_G : Sylow p G := default
  let P_H : Sylow p H := default

  -- Step 2.3: Cardinality of Sylow p-subgroups (in terms of Nat.card)
  have hG_nat : Nat.card G = p * q := by simp [Nat.card_eq_fintype_card, hG]
  have hH_nat : Nat.card H = p * q := by simp [Nat.card_eq_fintype_card, hH]

  have hcard_PG_nat : Nat.card ↥(P_G : Subgroup G) = p := by
    have h1' := Sylow.card_eq_multiplicity P_G
    rw [hG_nat] at h1'
    have h_mult_p : p.factorization p = 1 := Nat.Prime.factorization_self hp
    have h_mult_q : q.factorization p = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      right; left
      intro hdvd
      -- p ∣ q and both prime, so p = q, contradicting p ≠ q
      have := hq.eq_one_or_self_of_dvd p hdvd
      rcases this with rfl | rfl
      · exact absurd hp Nat.not_prime_one
      · exact hpq_ne rfl
    simp only [Nat.factorization_mul hp.ne_zero hq.ne_zero, Finsupp.add_apply,
      h_mult_p, h_mult_q, add_zero, pow_one] at h1'
    exact h1'

  have hcard_PG : Fintype.card ↥P_G = p := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard_PG_nat

  have hcard_PH_nat : Nat.card ↥(P_H : Subgroup H) = p := by
    have h1' := Sylow.card_eq_multiplicity P_H
    rw [hH_nat] at h1'
    have h_mult_p : p.factorization p = 1 := Nat.Prime.factorization_self hp
    have h_mult_q : q.factorization p = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      right; left
      intro hdvd
      -- p ∣ q and both prime, so p = q, contradicting p ≠ q
      have := hq.eq_one_or_self_of_dvd p hdvd
      rcases this with rfl | rfl
      · exact absurd hp Nat.not_prime_one
      · exact hpq_ne rfl
    simp only [Nat.factorization_mul hp.ne_zero hq.ne_zero, Finsupp.add_apply,
      h_mult_p, h_mult_q, add_zero, pow_one] at h1'
    exact h1'

  have hcard_PH : Fintype.card ↥P_H = p := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard_PH_nat

  /-
    Step 3: Show Sylow p-subgroups are normal.
    Number of Sylow p-subgroups divides q and is ≡ 1 (mod p).
    Since q < p, the only possibility is 1, making the Sylow p-subgroup unique and normal.
  -/
  -- Step 3.1: Compute the index of Sylow p-subgroup in G
  have h_index_G : (P_G : Subgroup G).index = q := by
    have h_card_mul := Subgroup.card_mul_index (P_G : Subgroup G)
    simp only [hcard_PG_nat, hG_nat] at h_card_mul
    exact Nat.eq_of_mul_eq_mul_left hp.pos h_card_mul

  have h_index_H : (P_H : Subgroup H).index = q := by
    have h_card_mul := Subgroup.card_mul_index (P_H : Subgroup H)
    simp only [hcard_PH_nat, hH_nat] at h_card_mul
    exact Nat.eq_of_mul_eq_mul_left hp.pos h_card_mul

  -- Step 3.2: G's Sylow p-subgroup is normal
  have hP_G_normal : (P_G : Subgroup G).Normal := by
    have h_dvd : Nat.card (Sylow p G) ∣ q := by
      have := Sylow.card_dvd_index P_G
      rwa [h_index_G] at this
    have h_cong : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
    -- Since card divides q (prime) and is ≡ 1 (mod p) with q < p, card = 1
    have h_one_or_q : Nat.card (Sylow p G) = 1 ∨ Nat.card (Sylow p G) = q :=
      hq.eq_one_or_self_of_dvd _ h_dvd
    have h_eq_1 : Nat.card (Sylow p G) = 1 := by
      rcases h_one_or_q with h_eq_1 | h_eq_q
      · exact h_eq_1
      · exfalso
        rw [h_eq_q] at h_cong
        have : p ∣ q - 1 := (Nat.modEq_iff_dvd' hq.one_le).mp h_cong.symm
        have hq_ge_2 : 2 ≤ q := hq.two_le
        have hq_sub_1_pos : 0 < q - 1 := by omega
        have : p ≤ q - 1 := Nat.le_of_dvd hq_sub_1_pos this
        omega
    haveI : Subsingleton (Sylow p G) := Finite.card_le_one_iff_subsingleton.mp (by
      rw [h_eq_1])
    exact Sylow.normal_of_subsingleton P_G

  -- Step 3.3: H's Sylow p-subgroup is normal (same argument)
  have hP_H_normal : (P_H : Subgroup H).Normal := by
    have h_dvd : Nat.card (Sylow p H) ∣ q := by
      have := Sylow.card_dvd_index P_H
      rwa [h_index_H] at this
    have h_cong : Nat.card (Sylow p H) ≡ 1 [MOD p] := card_sylow_modEq_one p H
    have h_one_or_q : Nat.card (Sylow p H) = 1 ∨ Nat.card (Sylow p H) = q :=
      hq.eq_one_or_self_of_dvd _ h_dvd
    have h_eq_1 : Nat.card (Sylow p H) = 1 := by
      rcases h_one_or_q with h_eq_1 | h_eq_q
      · exact h_eq_1
      · exfalso
        rw [h_eq_q] at h_cong
        have : p ∣ q - 1 := (Nat.modEq_iff_dvd' hq.one_le).mp h_cong.symm
        have hq_ge_2 : 2 ≤ q := hq.two_le
        have hq_sub_1_pos : 0 < q - 1 := by omega
        have : p ≤ q - 1 := Nat.le_of_dvd hq_sub_1_pos this
        omega
    haveI : Subsingleton (Sylow p H) := Finite.card_le_one_iff_subsingleton.mp (by
      rw [h_eq_1])
    exact Sylow.normal_of_subsingleton P_H

  /-
    Step 4: Get complements using Schur-Zassenhaus.
    The Sylow p-subgroup is normal with index q, and gcd(p, q) = 1.
    So a complement exists (which is a Sylow q-subgroup).
  -/
  -- Step 4.1: Complement for G
  have hcomp_G : ∃ Q_G : Subgroup G, (P_G : Subgroup G).IsComplement' Q_G := by
    apply Subgroup.exists_right_complement'_of_coprime
    rw [hcard_PG_nat, h_index_G]
    exact hpq_coprime

  obtain ⟨Q_G, hQ_G_comp⟩ := hcomp_G

  -- Step 4.2: Complement for H
  have hcomp_H : ∃ Q_H : Subgroup H, (P_H : Subgroup H).IsComplement' Q_H := by
    apply Subgroup.exists_right_complement'_of_coprime
    rw [hcard_PH_nat, h_index_H]
    exact hpq_coprime

  obtain ⟨Q_H, hQ_H_comp⟩ := hcomp_H

  /-
    Step 5: Establish cardinalities and cyclic structure.
  -/
  -- Step 5.1: Cardinality of Q_G is q
  have hcard_QG_nat : Nat.card ↥Q_G = q := by
    have h_comp := hQ_G_comp.card_mul
    simp only [hcard_PG_nat, hG_nat] at h_comp
    exact Nat.eq_of_mul_eq_mul_left hp.pos h_comp

  have hcard_QG : Fintype.card ↥Q_G = q := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard_QG_nat

  -- Step 5.2: Cardinality of Q_H is q
  have hcard_QH_nat : Nat.card ↥Q_H = q := by
    have h_comp := hQ_H_comp.card_mul
    simp only [hcard_PH_nat, hH_nat] at h_comp
    exact Nat.eq_of_mul_eq_mul_left hp.pos h_comp

  have hcard_QH : Fintype.card ↥Q_H = q := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard_QH_nat

  -- Step 5.3: All Sylow subgroups are cyclic (groups of prime order are cyclic)
  haveI : IsCyclic ↥(P_G : Subgroup G) := isCyclic_of_prime_card hcard_PG_nat

  haveI : IsCyclic ↥(P_H : Subgroup H) := isCyclic_of_prime_card hcard_PH_nat

  haveI : IsCyclic ↥Q_G := isCyclic_of_prime_card hcard_QG_nat

  haveI : IsCyclic ↥Q_H := isCyclic_of_prime_card hcard_QH_nat

  /-
    Step 6: The isomorphism between G and H

    At this point we have established:
    - G and H both have order pq with p > q primes and q | p-1
    - Both have unique normal Sylow p-subgroups P_G and P_H
    - Both have complements Q_G and Q_H (Sylow q-subgroups)
    - All these subgroups are cyclic (prime order)

    This is exactly the setup for the classification theorem: all nonabelian groups
    of order pq (with q | p-1) are isomorphic to the unique nonabelian semidirect
    product Z_p ⋊ Z_q.

    The formal proof that G ≅ H proceeds as follows:
    1. G ≅ P_G ⋊_φ Q_G and H ≅ P_H ⋊_ψ Q_H (semidirect products)
    2. P_G ≅ Z_p ≅ P_H and Q_G ≅ Z_q ≅ Q_H (cyclic of prime order)
    3. The actions φ and ψ are both nontrivial (G, H are nonabelian)
    4. Any two nontrivial actions Z_q → Aut(Z_p) give isomorphic semidirect products
       because Aut(Z_p) ≅ Z_{p-1} has a unique subgroup of order q

    Step 4 is the key: since q | p-1, the cyclic group Z_{p-1} has a unique subgroup
    of order q (cyclic groups have unique subgroups for each divisor). Both φ and ψ
    must map to this same subgroup, and any two generators of Z_q can be related
    by an automorphism of Z_q, making the semidirect products isomorphic.
  -/

  -- Step 6.1: Set up normality instances
  haveI : (P_G : Subgroup G).Normal := hP_G_normal
  haveI : (P_H : Subgroup H).Normal := hP_H_normal

  /-
    Step 6.2: The classification theorem approach using semidirect products.

    By `SemidirectProduct.mulEquivSubgroup`, we have:
    - G ≃* P_G ⋊[φ_G] Q_G  (where φ_G is the conjugation action)
    - H ≃* P_H ⋊[φ_H] Q_H  (where φ_H is the conjugation action)

    To show G ≃* H, we need to show: P_G ⋊[φ_G] Q_G ≃* P_H ⋊[φ_H] Q_H

    Using `SemidirectProduct.congr'`, we can construct this isomorphism from:
    - fP : P_G ≃* P_H (cyclic groups of order p)
    - fQ : Q_G ≃* Q_H (cyclic groups of order q)

    The `congr'` constructor automatically handles the action compatibility by
    transporting the action through the isomorphisms. This gives us:
    P_G ⋊[φ_G] Q_G ≃* P_H ⋊[φ'] Q_H
    where φ' = MulAut.congr fP ∘ φ_G ∘ fQ⁻¹

    The key mathematical fact is that φ_H and φ' must give isomorphic semidirect
    products because all nontrivial actions Z_q → Aut(Z_p) give isomorphic results
    when q | p-1 (they all have image in the unique order-q subgroup of Aut(Z_p)).
  -/

  -- Step 6.3: Get semidirect product decompositions via mulEquivSubgroup
  let φ_G : Q_G →* MulAut ↥(P_G : Subgroup G) :=
    ((P_G : Subgroup G).normalizerMonoidHom).comp
      (Subgroup.inclusion ((P_G : Subgroup G).normalizer_eq_top ▸ le_top))

  let φ_H : Q_H →* MulAut ↥(P_H : Subgroup H) :=
    ((P_H : Subgroup H).normalizerMonoidHom).comp
      (Subgroup.inclusion ((P_H : Subgroup H).normalizer_eq_top ▸ le_top))

  -- The semidirect product isomorphisms
  let sdp_G : (↥(P_G : Subgroup G)) ⋊[φ_G] (↥Q_G) ≃* G :=
    SemidirectProduct.mulEquivSubgroup hQ_G_comp

  let sdp_H : (↥(P_H : Subgroup H)) ⋊[φ_H] (↥Q_H) ≃* H :=
    SemidirectProduct.mulEquivSubgroup hQ_H_comp

  /-
    Step 6.4: Build the isomorphism using a carefully chosen fQ that makes actions compatible.

    The key insight: instead of using the "canonical" cyclic isomorphism for fQ and
    then trying to fix up the action mismatch, we construct fQ specifically so that
    the transported action φ' equals φ_H.

    Mathematical background:
    - Both G and H are nonabelian, so the conjugation actions φ_G and φ_H are nontrivial
    - Aut(P_H) ≅ (Z/pZ)× ≅ Z_{p-1} has a unique subgroup of order q (since q | p-1)
    - Both actions must have image in this unique subgroup
    - By choosing fQ appropriately (composing with an automorphism of Q_H), we can
      ensure the transported action matches

    The construction:
    1. fP : P_G ≃* P_H is the canonical cyclic isomorphism
    2. For fQ, we need to choose it so that for all g ∈ Q_G:
       MulAut.congr(fP)(φ_G(g)) = φ_H(fQ(g))

    This is equivalent to: fQ⁻¹ ∘ φ_H⁻¹ ∘ (MulAut.congr fP) ∘ φ_G = id on Q_G

    Since Q_G and Q_H are cyclic of prime order, we can construct such fQ by:
    - Let g_G ∈ Q_G be a generator
    - Let α = (MulAut.congr fP)(φ_G(g_G)) ∈ Aut(P_H) (nontrivial, order q)
    - Let β = φ_H(g_H) for some generator g_H ∈ Q_H (nontrivial, order q)
    - Since α and β are in the same cyclic subgroup of order q, β = α^k for some k
    - Define fQ(g_G) = g_H^(k⁻¹), which extends uniquely to a homomorphism
    - Then φ_H(fQ(g_G)) = φ_H(g_H^(k⁻¹)) = β^(k⁻¹) = α^(k·k⁻¹) = α = (MulAut.congr fP)(φ_G(g_G))

    For the formal proof, we use that any two nontrivial homomorphisms from a cyclic
    group of prime order q to a cyclic group of order q are related by an automorphism
    of the source. We construct fQ as the composition of the canonical isomorphism
    with this adjusting automorphism.
  -/

  -- Step 6.5: Build the canonical isomorphism for P
  let fP : ↥(P_G : Subgroup G) ≃* ↥(P_H : Subgroup H) :=
    mulEquivOfCyclicCardEq (hcard_PG_nat.trans hcard_PH_nat.symm)

  /-
    Step 7: The final isomorphism.

    Since we cannot easily construct the "correct" fQ without developing more
    machinery about cyclic group automorphisms and their interaction with
    conjugation actions, we take a different approach.

    Alternative approach: We construct an isomorphism by showing that both G and H
    are isomorphic to a common intermediate group. Specifically:

    1. Both G and H decompose as semidirect products P ⋊ Q with P ≅ Z_p, Q ≅ Z_q
    2. The conjugation action is nontrivial (since the groups are nonabelian)
    3. All nontrivial semidirect products Z_p ⋊ Z_q (with action of order q) are isomorphic

    Step 3 is the key: we show this by constructing an explicit isomorphism.

    The classification theorem states: there is exactly one nonabelian group of order pq
    (up to isomorphism) when q | p-1. This group can be presented as:
    ⟨a, b | a^p = 1, b^q = 1, bab⁻¹ = a^r⟩ where r is a primitive q-th root mod p.

    Both G and H satisfy this structure, hence G ≃* H.
  -/

  -- Step 7.1: For the formal isomorphism, we use the semidirect product decomposition
  -- but need to handle the action compatibility explicitly.

  -- We observe that both groups decompose as semidirect products with the SAME
  -- underlying groups (up to isomorphism) and with actions that are "equivalent"
  -- in the sense that they both generate the unique order-q subgroup of Aut(Z_p).

  -- The key mathematical fact we use:
  -- If φ, ψ : Z_q → Aut(Z_p) are both nontrivial homomorphisms, then
  -- Z_p ⋊_φ Z_q ≃* Z_p ⋊_ψ Z_q.

  -- Proof sketch:
  -- - Both φ and ψ have image in the unique order-q subgroup of Aut(Z_p)
  -- - Since Z_q is cyclic of prime order, φ and ψ are both surjective onto this subgroup
  -- - Therefore ker(φ) = ker(ψ) = {1} (both are injective)
  -- - The images Im(φ) = Im(ψ) = the unique order-q subgroup
  -- - For generators: φ(1) = α^i and ψ(1) = α^j for some generator α, with gcd(i,q)=gcd(j,q)=1
  -- - Define σ : Z_q → Z_q by σ(x) = (j·i⁻¹)·x
  -- - Then ψ = φ ∘ σ
  -- - The map (n, g) ↦ (n, σ⁻¹(g)) is an isomorphism Z_p ⋊_ψ Z_q → Z_p ⋊_φ Z_q

  -- Step 7.2: We construct the isomorphism G ≃* H using this approach.

  -- First, establish that the canonical cyclic isomorphism fQ exists
  let fQ_can : ↥Q_G ≃* ↥Q_H :=
    mulEquivOfCyclicCardEq (hcard_QG_nat.trans hcard_QH_nat.symm)

  -- Step 7.3: The action compatibility automorphism
  -- We need to find σ : Q_H ≃* Q_H such that for the transported action φ'
  -- (defined as MulAut.congr fP ∘ φ_G ∘ fQ_can.symm), we have φ_H = φ' ∘ σ.

  -- Since both φ' and φ_H are nontrivial homomorphisms from Q_H (cyclic of prime order q)
  -- to Aut(P_H) (which has a unique order-q subgroup), such σ exists.

  -- The isomorphism Z_p ⋊_φ' Z_q ≃* Z_p ⋊_φ_H Z_q is then given by (n, g) ↦ (n, σ⁻¹(g)).

  -- Step 7.4: For a fully constructive proof, we would need to:
  -- 1. Pick generators of Q_G and Q_H
  -- 2. Compute the images under φ_G and φ_H
  -- 3. Find the exponent relating these images
  -- 4. Construct σ using this exponent

  -- However, this requires explicit computation with representatives, which is complex.
  -- Instead, we use the existence result: such σ exists because both actions are nontrivial
  -- and map to the same (unique) target subgroup.

  -- Step 7.5: The final composition
  -- Let φ' be the transported action via the canonical isomorphisms:
  let φ' : Q_H →* MulAut ↥(P_H : Subgroup H) :=
    MonoidHom.comp (MulAut.congr fP) (φ_G.comp fQ_can.symm.toMonoidHom)

  -- We need: P_H ⋊[φ'] Q_H ≃* P_H ⋊[φ_H] Q_H
  -- This requires finding σ such that φ_H = φ' ∘ σ

  -- Since this is an existence theorem, we can use Classical.choice to select
  -- the required automorphism σ.

  -- Step 7.6: Show the required σ exists
  -- The existence follows from: both φ' and φ_H are nontrivial, hence surjective
  -- onto the unique order-q subgroup. Any two surjective homomorphisms from a
  -- cyclic group of prime order to the same group are related by an automorphism.

  have h_exists_sigma : ∃ (σ : ↥Q_H ≃* ↥Q_H),
      ∀ g : ↥Q_H, φ_H (σ g) = φ' g := by
    -- This is the key claim: such σ exists.
    -- The proof uses:
    -- 1. Q_H is cyclic of prime order q
    -- 2. Both φ' and φ_H are homomorphisms to Aut(P_H)
    -- 3. Aut(P_H) has exactly one subgroup of order q (since P_H ≅ Z_p and q | p-1)
    -- 4. Both φ' and φ_H must have image in this subgroup (or be trivial)
    -- 5. G nonabelian implies φ_G is nontrivial, hence φ' is nontrivial
    -- 6. H nonabelian implies φ_H is nontrivial

    -- For nontrivial homomorphisms from Z_q to a fixed cyclic group of order q,
    -- any two differ by an automorphism of Z_q.

    /-
      Mathematical argument:
      1. Show φ_G is nontrivial (from G being nonabelian)
      2. Show φ_H is nontrivial (from H being nonabelian)
      3. φ' is nontrivial (as transport of φ_G via isomorphisms)
      4. Both φ' and φ_H are nontrivial homs from Q_H (order q) to Aut(P_H)
      5. Since Q_H has prime order q, both are injective
      6. Both images lie in the unique order-q subgroup of Aut(P_H)
      7. Since q | p-1, Aut(P_H) ≅ Z_{p-1} has exactly one order-q subgroup
      8. So Im(φ') = Im(φ_H) = S, and both are isomorphisms Q_H → S
      9. Therefore σ := φ_H⁻¹ ∘ φ' (using that φ_H : Q_H → S is bijective)
         gives the required automorphism

      Step 1: Show that if the action is trivial, the group is abelian.
      For the semidirect product P ⋊_φ Q with trivial φ, we have (p,q) * (p',q') = (pp', qq')
      which is just the direct product, hence abelian when P and Q are abelian.
    -/

    -- The argument uses the structure of the semidirect product isomorphism.
    -- When φ_G or φ_H is trivial, the group is P × Q (direct product), hence abelian.

    -- Prove G nonabelian implies φ_G nontrivial
    have h_φ_G_nontrivial : φ_G ≠ 1 := by
      intro h_triv
      -- If φ_G = 1, then the semidirect product is just the direct product
      -- which is abelian when both factors are abelian (cyclic)
      obtain ⟨x, y, hxy⟩ := hG_nonab
      apply hxy

      let x' := sdp_G.symm x
      let y' := sdp_G.symm y

      -- Extract the components
      have h1 : φ_G x'.right = 1 := congrFun (congrArg DFunLike.coe h_triv) x'.right
      have h2 : φ_G y'.right = 1 := congrFun (congrArg DFunLike.coe h_triv) y'.right

      -- P_G and Q_G are cyclic hence abelian
      haveI hPG_comm : CommGroup ↥(P_G : Subgroup G) := IsCyclic.commGroup
      haveI hQG_comm : CommGroup ↥Q_G := IsCyclic.commGroup

      have h_comm_sdp : x' * y' = y' * x' := by
        -- In a semidirect product with trivial action, multiplication is componentwise
        -- and hence commutative when both factors are abelian
        -- P_G is cyclic and hence a commutative group
        have h_left : x'.left * y'.left = y'.left * x'.left :=
          IsCyclic.commutative.comm _ _
        have h_right : x'.right * y'.right = y'.right * x'.right :=
          IsCyclic.commutative.comm _ _
        -- The semidirect product formula: (p₁, q₁) * (p₂, q₂) = (p₁ * φ(q₁)(p₂), q₁ * q₂)
        -- When φ = 1: (p₁, q₁) * (p₂, q₂) = (p₁ * p₂, q₁ * q₂)
        ext <;> simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
          h1, h2, MulAut.one_apply, h_left, h_right]

      calc x * y = sdp_G (sdp_G.symm x) * sdp_G (sdp_G.symm y) := by simp
        _ = sdp_G (sdp_G.symm x * sdp_G.symm y) := by rw [map_mul]
        _ = sdp_G (sdp_G.symm y * sdp_G.symm x) := by rw [h_comm_sdp]
        _ = sdp_G (sdp_G.symm y) * sdp_G (sdp_G.symm x) := by rw [map_mul]
        _ = y * x := by simp

    -- Prove H nonabelian implies φ_H nontrivial
    have h_φ_H_nontrivial : φ_H ≠ 1 := by
      intro h_triv
      obtain ⟨x, y, hxy⟩ := hH_nonab
      apply hxy
      let x' := sdp_H.symm x
      let y' := sdp_H.symm y
      have h1 : φ_H x'.right = 1 := congrFun (congrArg DFunLike.coe h_triv) x'.right
      have h2 : φ_H y'.right = 1 := congrFun (congrArg DFunLike.coe h_triv) y'.right

      haveI hPH_comm : CommGroup ↥(P_H : Subgroup H) := IsCyclic.commGroup
      haveI hQH_comm : CommGroup ↥Q_H := IsCyclic.commGroup

      have h_comm_sdp : x' * y' = y' * x' := by
        have h_left : x'.left * y'.left = y'.left * x'.left :=
          IsCyclic.commutative.comm _ _
        have h_right : x'.right * y'.right = y'.right * x'.right :=
          IsCyclic.commutative.comm _ _
        ext <;> simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
          h1, h2, MulAut.one_apply, h_left, h_right]

      calc x * y = sdp_H (sdp_H.symm x) * sdp_H (sdp_H.symm y) := by simp
        _ = sdp_H (sdp_H.symm x * sdp_H.symm y) := by rw [map_mul]
        _ = sdp_H (sdp_H.symm y * sdp_H.symm x) := by rw [h_comm_sdp]
        _ = sdp_H (sdp_H.symm y) * sdp_H (sdp_H.symm x) := by rw [map_mul]
        _ = y * x := by simp

    -- Prove φ' is nontrivial (transport of nontrivial φ_G via isomorphisms)
    have h_φ'_nontrivial : φ' ≠ 1 := by
      intro h_triv
      apply h_φ_G_nontrivial
      -- We need to show φ_G = 1, i.e., for all g ∈ Q_G, φ_G g = 1
      ext g p
      simp only [MonoidHom.one_apply, MulAut.one_apply]
      -- φ' = MulAut.congr fP ∘ φ_G ∘ fQ_can.symm
      -- If φ' = 1, then for all h in Q_H: MulAut.congr fP (φ_G (fQ_can.symm h)) = 1
      -- Taking h = fQ_can g, we get MulAut.congr fP (φ_G g) = 1
      -- Since MulAut.congr fP is an isomorphism, φ_G g = 1
      have h_at_fQ_can_g : φ' (fQ_can g) = 1 := by
        have := congrFun (congrArg DFunLike.coe h_triv) (fQ_can g)
        simp only [MonoidHom.one_apply] at this
        exact this
      simp only [φ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply] at h_at_fQ_can_g
      -- MulAut.congr fP (φ_G g) = 1 means φ_G g = 1 since MulAut.congr fP is injective
      have h_congr_inj : Function.Injective (MulAut.congr fP) := MulEquiv.injective _
      have h_congr_eq : MulAut.congr fP (φ_G g) = 1 := h_at_fQ_can_g
      have h_φ_G_g_eq_1 : φ_G g = 1 := by
        have h_map_one : MulAut.congr fP 1 = 1 := MulEquiv.map_one _
        rw [← h_map_one] at h_congr_eq
        exact h_congr_inj h_congr_eq
      simp [h_φ_G_g_eq_1]

    -- Now we construct σ using that both φ' and φ_H are nontrivial
    -- and hence are both isomorphisms onto the unique order-q subgroup of Aut(P_H).

    -- Since Q_H is cyclic of prime order q, any nontrivial homomorphism is injective.
    -- Both φ' and φ_H are nontrivial, so both are injective.

    -- Since both images have order q and Aut(P_H) has a unique order-q subgroup,
    -- the images are identical.

    -- The automorphism σ = φ_H⁻¹ ∘ φ' (restricted to the common image) works.

    -- Use Classical.choice to select a preimage function
    -- For each g ∈ Q_H, we need σ(g) such that φ_H(σ g) = φ' g

    -- Since both maps are injective and have the same image, this is always possible.

    -- Define σ by: σ(g) is the unique element h such that φ_H(h) = φ'(g)
    -- This exists because Im(φ') = Im(φ_H) (both equal the unique order-q subgroup)

    -- The formal construction uses the fact that φ_H restricted to its image is bijective

    have h_φ_H_inj : Function.Injective φ_H := by
      -- Kernel of φ_H is a subgroup of Q_H
      -- Q_H has prime order q, so kernel is {1} or all of Q_H
      -- If kernel = Q_H, then φ_H = 1, contradicting h_φ_H_nontrivial
      -- So kernel = {1}, meaning φ_H is injective
      intro g₁ g₂ h_eq
      have h_ker : g₁ * g₂⁻¹ ∈ MonoidHom.ker φ_H := by
        simp only [MonoidHom.mem_ker, map_mul, map_inv, h_eq, mul_inv_cancel]
      -- Kernel is a subgroup of Q_H which has prime order q
      by_cases h_ker_triv : MonoidHom.ker φ_H = ⊥
      · simp only [h_ker_triv, Subgroup.mem_bot, mul_inv_eq_one] at h_ker
        exact h_ker
      · -- Kernel is not trivial, so it's all of Q_H (prime order)
        have h_ker_top : MonoidHom.ker φ_H = ⊤ := by
          -- Kernel divides |Q_H| = q (prime), so kernel has size 1 or q
          have h_ker_card_dvd : Nat.card (MonoidHom.ker φ_H) ∣ q := by
            rw [← hcard_QH_nat]
            exact Subgroup.card_subgroup_dvd_card (MonoidHom.ker φ_H)
          have := hq.eq_one_or_self_of_dvd _ h_ker_card_dvd
          rcases this with h_one | h_q
          · -- |ker| = 1 means ker = ⊥
            exfalso
            apply h_ker_triv
            exact Subgroup.eq_bot_of_card_eq _ h_one
          · -- |ker| = q = |Q_H| means ker = Q_H = ⊤
            rw [← hcard_QH_nat] at h_q
            exact Subgroup.eq_top_of_card_eq _ h_q
        -- But then φ_H = 1
        exfalso
        apply h_φ_H_nontrivial
        ext g
        have : g ∈ MonoidHom.ker φ_H := by rw [h_ker_top]; trivial
        simp only [MonoidHom.mem_ker] at this
        simp [this]

    have h_φ'_inj : Function.Injective φ' := by
      intro g₁ g₂ h_eq
      have h_ker : g₁ * g₂⁻¹ ∈ MonoidHom.ker φ' := by
        simp only [MonoidHom.mem_ker, map_mul, map_inv, h_eq, mul_inv_cancel]
      by_cases h_ker_triv : MonoidHom.ker φ' = ⊥
      · simp only [h_ker_triv, Subgroup.mem_bot, mul_inv_eq_one] at h_ker
        exact h_ker
      · have h_ker_top : MonoidHom.ker φ' = ⊤ := by
          have h_ker_card_dvd : Nat.card (MonoidHom.ker φ') ∣ q := by
            rw [← hcard_QH_nat]
            exact Subgroup.card_subgroup_dvd_card (MonoidHom.ker φ')
          have := hq.eq_one_or_self_of_dvd _ h_ker_card_dvd
          rcases this with h_one | h_q
          · exfalso; apply h_ker_triv; exact Subgroup.eq_bot_of_card_eq _ h_one
          · rw [← hcard_QH_nat] at h_q; exact Subgroup.eq_top_of_card_eq _ h_q
        exfalso
        apply h_φ'_nontrivial
        ext g
        have : g ∈ MonoidHom.ker φ' := by rw [h_ker_top]; trivial
        simp only [MonoidHom.mem_ker] at this
        simp [this]

    -- Both images are subgroups of order q in Aut(P_H)
    -- Aut(P_H) ≅ Z_{p-1} is cyclic, and q | p-1, so there's a unique order-q subgroup

    -- The key fact: any element in Im(φ') is in Im(φ_H) and vice versa

    -- For each g ∈ Q_H, since φ'(g) ∈ Im(φ_H), there exists unique h with φ_H(h) = φ'(g)
    -- Define σ(g) = h

    -- Classical construction of σ
    -- Key fact: range(φ_H) = range(φ') because both are cyclic subgroups of order q
    -- in MulAut(P_H), and P_H is cyclic of prime order p, so MulAut(P_H) is cyclic
    -- of order p-1. Since q | p-1, there's a unique subgroup of order q.

    -- For the formal proof, we use that both φ_H and φ' are injective bijections
    -- from Q_H to cyclic subgroups of order q. In a cyclic group, there is at most
    -- one subgroup of each divisor order.

    -- The proof proceeds as follows:
    -- 1. Both φ_H and φ' induce isomorphisms from Q_H to their images
    -- 2. Both images have cardinality q (injective map from order-q group)
    -- 3. MulAut(P_H) is cyclic (as P_H ≅ Z_p has Aut(Z_p) ≅ Z_{p-1})
    -- 4. A cyclic group has unique subgroup of each divisor order
    -- 5. Therefore range(φ_H) = range(φ')

    -- For now, we encapsulate this argument:
    have h_ranges_eq : MonoidHom.range φ_H = MonoidHom.range φ' := by
      /-
        Proof outline:
        1. Both φ_H and φ' are injective (proved above as h_φ_H_inj, h_φ'_inj)
        2. Both ranges have cardinality q (Q_H has order q and the maps are injective)
        3. MulAut(P_H) is cyclic (P_H is cyclic of prime order p, so Aut(P_H) ≅ Z_{p-1})
        4. In a cyclic group, two subgroups of the same cardinality are equal
        5. Therefore range(φ_H) = range(φ')
      -/

      -- Step 1: MulAut(P_H) is cyclic
      haveI h_aut_cyclic : IsCyclic (MulAut ↥(P_H : Subgroup H)) := by
        -- P_H is cyclic, so MulAut(P_H) is cyclic
        -- IsCyclic.mulAutMulEquiv gives: MulAut G ≃* (ZMod (Nat.card G))ˣ for cyclic G
        -- For prime p, (ZMod p)ˣ is cyclic of order p-1
        -- We use that subgroups of cyclic groups are cyclic
        have h_equiv : MulAut ↥(P_H : Subgroup H) ≃* (ZMod (Nat.card ↥(P_H : Subgroup H)))ˣ :=
          IsCyclic.mulAutMulEquiv ↥(P_H : Subgroup H)
        rw [hcard_PH_nat] at h_equiv
        exact h_equiv.isCyclic.mpr inferInstance

      -- Step 2: Both ranges have cardinality q
      have h_card_range_φ_H : Nat.card (MonoidHom.range φ_H) = q := by
        have h_bij : Function.Bijective (φ_H.rangeRestrict) := by
          constructor
          · intro x y hxy
            simp only [MonoidHom.rangeRestrict, MonoidHom.codRestrict_apply, Subtype.mk.injEq] at hxy
            exact h_φ_H_inj hxy
          · exact MonoidHom.rangeRestrict_surjective φ_H
        rw [← Nat.card_congr (Equiv.ofBijective _ h_bij)]
        exact hcard_QH_nat

      have h_card_range_φ' : Nat.card (MonoidHom.range φ') = q := by
        have h_bij : Function.Bijective (φ'.rangeRestrict) := by
          constructor
          · intro x y hxy
            simp only [MonoidHom.rangeRestrict, MonoidHom.codRestrict_apply, Subtype.mk.injEq] at hxy
            exact h_φ'_inj hxy
          · exact MonoidHom.rangeRestrict_surjective φ'
        rw [← Nat.card_congr (Equiv.ofBijective _ h_bij)]
        exact hcard_QH_nat

      -- Step 3: In cyclic MulAut(P_H), subgroups of same cardinality are equal
      have h_card_eq : Nat.card (MonoidHom.range φ_H) = Nat.card (MonoidHom.range φ') := by
        rw [h_card_range_φ_H, h_card_range_φ']

      -- Apply the unique subgroup theorem for cyclic groups
      -- Key lemma: In a cyclic group, subgroups with the same cardinality are equal
      -- This follows from: subgroups are cyclic, and there's a unique cyclic subgroup
      -- of each divisor order

      -- Use Bezout-based argument: in cyclic G of order n, the unique subgroup of order d
      -- (where d | n) is generated by g^(n/d) for any generator g. Since both ranges
      -- have order q and MulAut(P_H) is cyclic, they must be equal.

      -- The formal argument uses that two generators of the same order in a cyclic group
      -- generate the same subgroup. Both range(φ_H) and range(φ') are cyclic subgroups
      -- of order q in the cyclic group MulAut(P_H), so they're equal.

      -- Get generators of the ranges
      haveI h_range_H_cyclic : IsCyclic (MonoidHom.range φ_H) := Subgroup.isCyclic _
      haveI h_range_φ'_cyclic : IsCyclic (MonoidHom.range φ') := Subgroup.isCyclic _

      -- Both ranges are subgroups of a cyclic group with the same cardinality
      -- In a cyclic group, subgroups are uniquely determined by their order

      -- Use the general theorem: in cyclic G, H = K when |H| = |K|
      -- This requires proving that cyclic groups have unique subgroups of each divisor order

      -- The proof proceeds by showing both equal zpowers(gen^(|G|/q)) for any generator gen

      -- Direct approach: show both ranges are equal to the unique order-q subgroup
      obtain ⟨gen_aut, hgen_aut⟩ := IsCyclic.exists_generator (α := MulAut ↥(P_H : Subgroup H))

      -- Every element of the range is in zpowers(gen_aut)
      have h_range_H_le : MonoidHom.range φ_H ≤ Subgroup.zpowers gen_aut := by
        intro x hx
        exact hgen_aut x

      have h_range_φ'_le : MonoidHom.range φ' ≤ Subgroup.zpowers gen_aut := by
        intro x hx
        exact hgen_aut x

      -- In a cyclic group, the unique subgroup of order q is zpowers(gen^(|G|/q))
      -- Since both ranges have order q and are subgroups of zpowers(gen), they're equal

      -- Both ranges are cyclic subgroups of order q in the cyclic group MulAut(P_H)
      -- They each have a generator of order q in MulAut(P_H)
      -- Elements of the same order in a cyclic group generate the same subgroup

      obtain ⟨gen_H_range, hgen_H_range⟩ := IsCyclic.exists_generator (α := MonoidHom.range φ_H)
      obtain ⟨gen_φ'_range, hgen_φ'_range⟩ := IsCyclic.exists_generator (α := MonoidHom.range φ')

      -- orderOf(gen_H_range : MulAut P_H) = q
      have h_gen_H_range_top : Subgroup.zpowers gen_H_range = ⊤ := by
        ext x; simp only [Subgroup.mem_top, iff_true]; exact hgen_H_range x

      have h_ord_gen_H_range : orderOf gen_H_range = q := by
        rw [← Nat.card_zpowers gen_H_range, h_gen_H_range_top, Subgroup.card_top]
        exact h_card_range_φ_H

      -- orderOf(gen_φ'_range : MulAut P_H) = q
      have h_gen_φ'_range_top : Subgroup.zpowers gen_φ'_range = ⊤ := by
        ext x; simp only [Subgroup.mem_top, iff_true]; exact hgen_φ'_range x

      have h_ord_gen_φ'_range : orderOf gen_φ'_range = q := by
        rw [← Nat.card_zpowers gen_φ'_range, h_gen_φ'_range_top, Subgroup.card_top]
        exact h_card_range_φ'

      -- The coe's of the generators have the same order in MulAut(P_H)
      have h_ord_H_coe : orderOf (gen_H_range : MulAut ↥(P_H : Subgroup H)) = q := by
        rw [Subgroup.orderOf_coe gen_H_range, h_ord_gen_H_range]

      have h_ord_φ'_coe : orderOf (gen_φ'_range : MulAut ↥(P_H : Subgroup H)) = q := by
        rw [Subgroup.orderOf_coe gen_φ'_range, h_ord_gen_φ'_range]

      have h_ord_eq_coe : orderOf (gen_H_range : MulAut ↥(P_H : Subgroup H)) =
                          orderOf (gen_φ'_range : MulAut ↥(P_H : Subgroup H)) := by
        rw [h_ord_H_coe, h_ord_φ'_coe]

      -- In cyclic MulAut(P_H), elements of the same order generate the same zpowers
      -- This uses: in cyclic G, zpowers(x) = zpowers(y) when orderOf x = orderOf y

      -- Key lemma for cyclic groups: elements of the same order generate the same subgroup
      -- Proof: Let G = ⟨g⟩ with |G| = n. If orderOf(x) = orderOf(y) = d,
      -- then x = g^(n/d * k) and y = g^(n/d * m) for some k, m coprime to d.
      -- So zpowers(x) = zpowers(g^(n/d)) = zpowers(y).

      -- Apply Bezout-style argument for equality of zpowers
      have h_zpowers_eq : Subgroup.zpowers (gen_H_range : MulAut ↥(P_H : Subgroup H)) =
                          Subgroup.zpowers (gen_φ'_range : MulAut ↥(P_H : Subgroup H)) := by
        -- Both elements have order q in cyclic group MulAut(P_H)
        -- In a cyclic group, elements of the same order generate the same subgroup

        -- Get a generator of MulAut(P_H)
        obtain ⟨g_aut, hg_aut⟩ := IsCyclic.exists_generator (α := MulAut ↥(P_H : Subgroup H))

        -- g_aut generates MulAut(P_H)
        have h_gaut_top : Subgroup.zpowers g_aut = ⊤ := by
          ext x; simp only [Subgroup.mem_top, iff_true]; exact hg_aut x

        have h_ord_gaut : orderOf g_aut = Nat.card (MulAut ↥(P_H : Subgroup H)) := by
          rw [← Nat.card_zpowers g_aut, h_gaut_top, Subgroup.card_top]

        -- gen_H_range = g_aut^i for some i
        have h_mem_H : (gen_H_range : MulAut ↥(P_H : Subgroup H)) ∈ Subgroup.zpowers g_aut :=
          hg_aut _
        rw [mem_zpowers_iff_mem_range_orderOf] at h_mem_H
        simp only [Finset.mem_image, Finset.mem_range] at h_mem_H
        obtain ⟨i, _, hi⟩ := h_mem_H

        -- gen_φ'_range = g_aut^j for some j
        have h_mem_φ' : (gen_φ'_range : MulAut ↥(P_H : Subgroup H)) ∈ Subgroup.zpowers g_aut :=
          hg_aut _
        rw [mem_zpowers_iff_mem_range_orderOf] at h_mem_φ'
        simp only [Finset.mem_image, Finset.mem_range] at h_mem_φ'
        obtain ⟨j, _, hj⟩ := h_mem_φ'

        -- Key: zpowers(g^k) = zpowers(g^(gcd(k, orderOf g)))
        -- Use Bezout: gcd(k, n) = a*k + b*n for some a, b
        -- So g^(gcd(k,n)) = (g^k)^a, meaning g^(gcd(k,n)) ∈ zpowers(g^k)

        -- Lemma: g^d ∈ zpowers(g^k) when d = gcd(k, orderOf g)
        have h_gcd_mem : ∀ (g' : MulAut ↥(P_H : Subgroup H)) (k' : ℕ),
            g' ^ (k'.gcd (orderOf g')) ∈ Subgroup.zpowers (g' ^ k') := by
          intro g' k'
          rw [Subgroup.mem_zpowers_iff]
          set d := k'.gcd (orderOf g')
          obtain hab := Nat.gcd_eq_gcd_ab k' (orderOf g')
          use k'.gcdA (orderOf g')
          have h1 : (g' ^ k') ^ k'.gcdA (orderOf g') = g' ^ (↑k' * k'.gcdA (orderOf g')) := by
            rw [← zpow_natCast g' k', zpow_mul, zpow_natCast]
          rw [h1]
          have h2 : (↑k' : ℤ) * k'.gcdA (orderOf g') = ↑d - ↑(orderOf g') * k'.gcdB (orderOf g') := by
            have := hab; linarith
          rw [h2, zpow_sub, zpow_mul]
          simp only [zpow_natCast, pow_orderOf_eq_one, one_zpow, inv_one, mul_one]

        -- zpowers(g^i) = zpowers(g^(gcd(i, orderOf g)))
        have h_zpow_i : Subgroup.zpowers (g_aut ^ i) =
                        Subgroup.zpowers (g_aut ^ (i.gcd (orderOf g_aut))) := by
          apply le_antisymm
          · apply Subgroup.zpowers_le.mpr
            rw [Subgroup.mem_zpowers_iff]
            have hdiv : i.gcd (orderOf g_aut) ∣ i := Nat.gcd_dvd_left _ _
            obtain ⟨m, hm⟩ := hdiv
            use (m : ℤ)
            have h_goal : (g_aut ^ (i.gcd (orderOf g_aut))) ^ (m : ℤ) = g_aut ^ i := by
              calc (g_aut ^ (i.gcd (orderOf g_aut))) ^ (m : ℤ)
                  = g_aut ^ (((i.gcd (orderOf g_aut)) : ℤ) * (m : ℤ)) := by
                      rw [← zpow_natCast g_aut _, zpow_mul]
                _ = g_aut ^ (↑(i.gcd (orderOf g_aut) * m) : ℤ) := by norm_cast
                _ = g_aut ^ (i.gcd (orderOf g_aut) * m) := zpow_natCast g_aut _
                _ = g_aut ^ i := by rw [← hm]
            exact h_goal
          · apply Subgroup.zpowers_le.mpr
            exact h_gcd_mem g_aut i

        -- zpowers(g^j) = zpowers(g^(gcd(j, orderOf g)))
        have h_zpow_j : Subgroup.zpowers (g_aut ^ j) =
                        Subgroup.zpowers (g_aut ^ (j.gcd (orderOf g_aut))) := by
          apply le_antisymm
          · apply Subgroup.zpowers_le.mpr
            rw [Subgroup.mem_zpowers_iff]
            have hdiv : j.gcd (orderOf g_aut) ∣ j := Nat.gcd_dvd_left _ _
            obtain ⟨m, hm⟩ := hdiv
            use (m : ℤ)
            have h_goal : (g_aut ^ (j.gcd (orderOf g_aut))) ^ (m : ℤ) = g_aut ^ j := by
              calc (g_aut ^ (j.gcd (orderOf g_aut))) ^ (m : ℤ)
                  = g_aut ^ (((j.gcd (orderOf g_aut)) : ℤ) * (m : ℤ)) := by
                      rw [← zpow_natCast g_aut _, zpow_mul]
                _ = g_aut ^ (↑(j.gcd (orderOf g_aut) * m) : ℤ) := by norm_cast
                _ = g_aut ^ (j.gcd (orderOf g_aut) * m) := zpow_natCast g_aut _
                _ = g_aut ^ j := by rw [← hm]
            exact h_goal
          · apply Subgroup.zpowers_le.mpr
            exact h_gcd_mem g_aut j

        -- orderOf(g^i) = q, orderOf(g^j) = q
        have h_ord_gi_eq_q : orderOf (g_aut ^ i) = q := by rw [hi, h_ord_H_coe]
        have h_ord_gj_eq_q : orderOf (g_aut ^ j) = q := by rw [hj, h_ord_φ'_coe]

        -- q > 0 because q is prime
        have hq_pos : 0 < q := hq.pos

        -- i ≠ 0 and j ≠ 0 (since g_aut^i and g_aut^j have order q > 1)
        have h_i_ne_0 : i ≠ 0 := by
          intro hi_eq
          rw [hi_eq, pow_zero] at h_ord_gi_eq_q
          simp only [orderOf_one] at h_ord_gi_eq_q
          exact hq.ne_one h_ord_gi_eq_q.symm

        have h_j_ne_0 : j ≠ 0 := by
          intro hj_eq
          rw [hj_eq, pow_zero] at h_ord_gj_eq_q
          simp only [orderOf_one] at h_ord_gj_eq_q
          exact hq.ne_one h_ord_gj_eq_q.symm

        have h_pos_gcd_i : i.gcd (orderOf g_aut) ≠ 0 :=
          Nat.gcd_ne_zero_right (orderOf_pos g_aut).ne'
        have h_pos_gcd_j : j.gcd (orderOf g_aut) ≠ 0 :=
          Nat.gcd_ne_zero_right (orderOf_pos g_aut).ne'

        have h_ord_gi : orderOf (g_aut ^ i) = orderOf g_aut / (orderOf g_aut).gcd i :=
          orderOf_pow' g_aut h_i_ne_0

        have h_ord_gj : orderOf (g_aut ^ j) = orderOf g_aut / (orderOf g_aut).gcd j :=
          orderOf_pow' g_aut h_j_ne_0

        -- Therefore gcd(i, orderOf g) = gcd(j, orderOf g)
        have h_gcd_i_eq : i.gcd (orderOf g_aut) = j.gcd (orderOf g_aut) := by
          have h_eq : orderOf g_aut / (orderOf g_aut).gcd i =
                      orderOf g_aut / (orderOf g_aut).gcd j := by
            rw [← h_ord_gi, ← h_ord_gj, h_ord_gi_eq_q, h_ord_gj_eq_q]
          have h_pos : 0 < orderOf g_aut := orderOf_pos g_aut
          have h_dvd_i : (orderOf g_aut).gcd i ∣ orderOf g_aut := Nat.gcd_dvd_left _ _
          have h_dvd_j : (orderOf g_aut).gcd j ∣ orderOf g_aut := Nat.gcd_dvd_left _ _
          have h_ne_i : (orderOf g_aut).gcd i ≠ 0 := by rw [Nat.gcd_comm]; exact h_pos_gcd_i
          have h_ne_j : (orderOf g_aut).gcd j ≠ 0 := by rw [Nat.gcd_comm]; exact h_pos_gcd_j
          have h_div_pos : 0 < orderOf g_aut / (orderOf g_aut).gcd j := by
            apply Nat.div_pos
            · exact Nat.le_of_dvd h_pos h_dvd_j
            · exact Nat.pos_of_ne_zero h_ne_j
          have h_mul_i : (orderOf g_aut).gcd i * (orderOf g_aut / (orderOf g_aut).gcd j) =
                         orderOf g_aut := by
            rw [← h_eq, Nat.mul_div_cancel' h_dvd_i]
          have h_mul_j : (orderOf g_aut).gcd j * (orderOf g_aut / (orderOf g_aut).gcd j) =
                         orderOf g_aut := Nat.mul_div_cancel' h_dvd_j
          have h_mul_eq : (orderOf g_aut).gcd i * (orderOf g_aut / (orderOf g_aut).gcd j) =
                          (orderOf g_aut).gcd j * (orderOf g_aut / (orderOf g_aut).gcd j) := by
            rw [h_mul_i, h_mul_j]
          have h_gcd_eq' : (orderOf g_aut).gcd i = (orderOf g_aut).gcd j :=
            Nat.eq_of_mul_eq_mul_right h_div_pos h_mul_eq
          rw [Nat.gcd_comm, Nat.gcd_comm (orderOf g_aut) j] at h_gcd_eq'
          exact h_gcd_eq'

        -- zpowers(g^i) = zpowers(g^(gcd)) = zpowers(g^j)
        rw [← hi, ← hj, h_zpow_i, h_zpow_j, h_gcd_i_eq]

      -- Now show range(φ_H) = zpowers(gen_H_range : MulAut P_H)
      have h_range_H_eq : (MonoidHom.range φ_H : Set (MulAut ↥(P_H : Subgroup H))) =
                          Subgroup.zpowers (gen_H_range : MulAut ↥(P_H : Subgroup H)) := by
        ext x
        rw [SetLike.mem_coe, SetLike.mem_coe]
        constructor
        · intro hx
          have h_mem : (⟨x, hx⟩ : MonoidHom.range φ_H) ∈ Subgroup.zpowers gen_H_range :=
            hgen_H_range ⟨x, hx⟩
          rw [Subgroup.mem_zpowers_iff] at h_mem ⊢
          obtain ⟨k, hk⟩ := h_mem
          use k
          -- hk : gen_H_range ^ k = ⟨x, hx⟩
          -- Goal: ↑gen_H_range ^ k = x
          have hk' : (gen_H_range ^ k : MonoidHom.range φ_H).val = x := by
            rw [hk]
          simp only [← SubgroupClass.coe_zpow, hk']
        · intro hx
          rw [Subgroup.mem_zpowers_iff] at hx
          obtain ⟨k, hk⟩ := hx
          rw [← hk]
          exact Subgroup.zpow_mem _ gen_H_range.2 k

      have h_range_φ'_eq : (MonoidHom.range φ' : Set (MulAut ↥(P_H : Subgroup H))) =
                           Subgroup.zpowers (gen_φ'_range : MulAut ↥(P_H : Subgroup H)) := by
        ext x
        rw [SetLike.mem_coe, SetLike.mem_coe]
        constructor
        · intro hx
          have h_mem : (⟨x, hx⟩ : MonoidHom.range φ') ∈ Subgroup.zpowers gen_φ'_range :=
            hgen_φ'_range ⟨x, hx⟩
          rw [Subgroup.mem_zpowers_iff] at h_mem ⊢
          obtain ⟨k, hk⟩ := h_mem
          use k
          have hk' : (gen_φ'_range ^ k : MonoidHom.range φ').val = x := by
            rw [hk]
          simp only [← SubgroupClass.coe_zpow, hk']
        · intro hx
          rw [Subgroup.mem_zpowers_iff] at hx
          obtain ⟨k, hk⟩ := hx
          rw [← hk]
          exact Subgroup.zpow_mem _ gen_φ'_range.2 k

      -- Finally, range(φ_H) = range(φ')
      ext x
      rw [← SetLike.mem_coe, ← SetLike.mem_coe, h_range_H_eq, h_range_φ'_eq, h_zpowers_eq]

    have h_surj : ∀ g : ↥Q_H, ∃ h : ↥Q_H, φ_H h = φ' g := by
      intro g
      -- φ'(g) ∈ range(φ') = range(φ_H)
      have h_mem : φ' g ∈ MonoidHom.range φ_H := by
        rw [h_ranges_eq, MonoidHom.mem_range]
        use g
      exact h_mem

    -- Define σ using Classical.choose
    let σ_fun : ↥Q_H → ↥Q_H := fun g => Classical.choose (h_surj g)
    have hσ_fun : ∀ g, φ_H (σ_fun g) = φ' g := fun g => Classical.choose_spec (h_surj g)

    -- Show σ_fun is a group homomorphism
    have h_σ_hom : ∀ g₁ g₂, σ_fun (g₁ * g₂) = σ_fun g₁ * σ_fun g₂ := by
      intro g₁ g₂
      apply h_φ_H_inj
      rw [hσ_fun, map_mul]
      -- Goal: φ' (g₁ * g₂) = φ_H (σ_fun g₁) * φ_H (σ_fun g₂)
      rw [map_mul, hσ_fun, hσ_fun]

    -- Show σ_fun is bijective
    have h_σ_bij : Function.Bijective σ_fun := by
      constructor
      · -- Injective
        intro g₁ g₂ h_eq
        apply h_φ'_inj
        rw [← hσ_fun, ← hσ_fun, h_eq]
      · -- Surjective
        intro h
        -- Need to find g such that σ_fun(g) = h
        -- This means φ_H(σ_fun(g)) = φ_H(h), i.e., φ'(g) = φ_H(h)
        -- Since φ_H(h) ∈ range(φ_H) = range(φ'), there exists g with φ'(g) = φ_H(h)
        have h_mem : φ_H h ∈ MonoidHom.range φ' := by
          rw [← h_ranges_eq, MonoidHom.mem_range]
          use h
        obtain ⟨g, hg⟩ := h_mem
        use g
        -- We have φ'(g) = φ_H(h) and φ_H(σ_fun(g)) = φ'(g)
        -- So φ_H(σ_fun(g)) = φ_H(h), hence σ_fun(g) = h by injectivity
        apply h_φ_H_inj
        rw [hσ_fun, hg]

    -- Construct the MulEquiv
    -- First construct the MonoidHom
    let σ_hom : ↥Q_H →* ↥Q_H := {
      toFun := σ_fun
      map_one' := by
        apply h_φ_H_inj
        rw [hσ_fun, map_one, map_one]
      map_mul' := h_σ_hom
    }
    use MulEquiv.ofBijective σ_hom h_σ_bij
    intro g
    exact hσ_fun g

  -- Step 7.7: Use σ to build the isomorphism between semidirect products
  obtain ⟨σ, hσ⟩ := h_exists_sigma

  -- Step 7.8: Build the isomorphism P_H ⋊[φ'] Q_H ≃* P_H ⋊[φ_H] Q_H
  let action_match : (↥(P_H : Subgroup H)) ⋊[φ'] (↥Q_H) ≃*
                     (↥(P_H : Subgroup H)) ⋊[φ_H] (↥Q_H) := by
    -- The isomorphism is (p, g) ↦ (p, σ g)
    -- This is a group homomorphism because:
    -- (p₁, g₁) * (p₂, g₂) = (p₁ * φ'(g₁)(p₂), g₁ * g₂)  in the source
    -- maps to (p₁ * φ'(g₁)(p₂), σ(g₁) * σ(g₂)) = (p₁ * φ_H(σ g₁)(p₂), σ(g₁) * σ(g₂))
    -- = (p₁, σ g₁) * (p₂, σ g₂) in the target  ✓ (using hσ: φ_H(σ g) = φ' g)

    -- Construct using congr with identity on P_H and σ on Q_H
    exact SemidirectProduct.congr (MulEquiv.refl _) σ (fun g => by
      ext p
      simp only [MulEquiv.trans_apply, MulEquiv.refl_apply]
      rw [← hσ g])

  -- Step 7.9: Compose all the isomorphisms
  -- G →[sdp_G.symm]→ P_G ⋊[φ_G] Q_G →[sdp_congr]→ P_H ⋊[φ'] Q_H →[action_match]→ P_H ⋊[φ_H] Q_H →[sdp_H]→ H
  -- MulEquiv.trans applies left-to-right: (a.trans b) x = b (a x)

  let sdp_congr : (↥(P_G : Subgroup G)) ⋊[φ_G] (↥Q_G) ≃*
                  (↥(P_H : Subgroup H)) ⋊[φ'] (↥Q_H) :=
    SemidirectProduct.congr' fP fQ_can

  -- Compose in order: sdp_G.symm : G ≃* P_G⋊Q_G, then sdp_congr : P_G⋊Q_G ≃* P_H⋊[φ']Q_H,
  -- then action_match : P_H⋊[φ']Q_H ≃* P_H⋊[φ_H]Q_H, then sdp_H : P_H⋊[φ_H]Q_H ≃* H
  exact ⟨sdp_G.symm.trans (sdp_congr.trans (action_match.trans sdp_H))⟩
