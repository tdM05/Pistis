import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $p$ is a prime and $G$ is a group of order $p^{\alpha}$ for some $\alpha \in \mathbb{Z}^{+}$, then every subgroup of index $p$ is normal in $G$.
-/

/-Informal Proof

Solution: Let $G$ be a group of order $p^k$ and $H \leq G$ a subgroup with $[G: H]=p$. Now $G$ acts on the conjugates $g H g^{-1}$ by conjugation, since
$$
g_1 g_2 \cdot H=\left(g_1 g_2\right) H\left(g_1 g_2\right)^{-1}=g_1\left(g_2 H g_2^{-1}\right) g_1^{-1}=g_1 \cdot\left(g_2 \cdot H\right)
$$
and $1 \cdot H=1 H 1=H$. Moreover, under this action we have $H \leq \operatorname{stab}(H)$. By Exercise 3.2.11, we have
$$
[G: \operatorname{stab}(H)][\operatorname{stab}(H): H]=[G: H]=p,
$$
a prime.
If $[G: \operatorname{stab}(H)]=p$, then $[\operatorname{stab}(H): H]=1$ and we have $H=\operatorname{stab}(H)$; moreover, $H$ has exactly $p$ conjugates in $G$. Let $\varphi: G \rightarrow S_p$ be the permutation representation induced by the action of $G$ on the conjugates of $H$, and let $K$ be the kernel of this representation. Now $K \leq \operatorname{stab}(H)=H$. By the first isomorphism theorem, the induced map $\bar{\varphi}: G / K \rightarrow S_p$ is injective, so that $|G / K|$ divides $p$ !. Note, however, that $|G / K|$ is a power of $p$ and that the only powers of $p$ that divide $p$ ! are 1 and $p$. So $[G: K]$ is 1 or $p$. If $[G: K]=1$, then $G=K$ so that $g H g^{-1}=H$ for all $g \in G$; then $\operatorname{stab}(H)=G$ and we have $[G: \operatorname{stab}(H)]=1$, a contradiction. Now suppose $[G: K]=p$. Again by Exercise $3.2$.11 we have $[G: K]=[G: H][H: K]$, so that $[H: K]=1$, hence $H=K$. Again, this implies that $H$ is normal so that $g H g^{-1}=H$ for all $g \in G$, and we have $[G: \operatorname{stab}(H)]=1$, a contradiction. Thus $[G: \operatorname{stab}(H)] \neq p$
If $[G: \operatorname{stab}(H)]=1$, then $G=\operatorname{stab}(H)$. That is, $g H g^{-1}=H$ for all $g \in G$; thus $H \leq G$ is normal.
-/

theorem Dummit_Foote_exercise_4_2_9a {G : Type*} [Fintype G] [Group G] {p α : ℕ}
  (hp : p.Prime) (ha : α > 0) (hG : card G = p ^ α) :
  ∀ H : Subgroup G, H.index = p → H.Normal := by
  -- Step 0: Work classically so we can freely choose elements and use choice-driven lemmas.
  classical
  -- Step 0.1: Introduce the arbitrary subgroup `H` with index `p`.
  intro H hH
  -- Step 1: Record the cardinality identity so it can be reused throughout the argument.
  have hCardPow : card G = p ^ α := hG
  -- Step 2: Record that `α ≠ 0`, needed to prove that `p` divides `p ^ α`.
  have hαne : α ≠ 0 := Nat.pos_iff_ne_zero.mp ha
  -- Step 3: Show that `p` divides `card G` by reducing to the obvious divisibility `p ∣ p ^ α`.
  have hpdvdCard : p ∣ card G := by
    -- Step 3.1: Reduce to `p ∣ p ^ α` using the equality `card G = p ^ α`.
    refine hCardPow ▸ ?_
    -- Step 3.2: Write `α = k + 1` to express `p ^ α` as `p * p ^ k`, which is visibly divisible by `p`.
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hαne
    subst hk
    -- Step 3.2.1: Exhibit the explicit multiple showing the divisibility.
    have : p ∣ p ^ Nat.succ k := by
      refine ⟨p ^ k, ?_⟩
      -- Step 3.2.1.1: Expand the power and rearrange to put the factor `p` first.
      simp [Nat.pow_succ, Nat.mul_comm]
    -- Step 3.2.2: The goal now literally matches `this`.
    exact this
  -- Step 4: Deduce that `card G` cannot be 1, otherwise `p` would divide 1.
  have hCard_ne_one : card G ≠ 1 := by
    -- Step 4.1: `p ∣ card G` together with `card G = 1` would force `p ∣ 1`, contradicting primality.
    intro hCard
    obtain ⟨d, hd⟩ := hpdvdCard
    have : p ∣ 1 := by
      refine ⟨d, ?_⟩
      simpa [hCard] using hd
    exact hp.not_dvd_one this
  -- Step 5: Isolate the minimal prime factor of `card G` and show it must equal `p`.
  have hMinFacPrime : (card G).minFac.Prime :=
    Nat.minFac_prime hCard_ne_one
  -- Step 5.1: The minimal prime factor divides `p ^ α` thanks to the earlier cardinality identity.
  have hMinFac_dvd_pow : (card G).minFac ∣ p ^ α := by
    -- `Nat.minFac_dvd` tells us the minimal prime factor divides the number itself.
    have : (card G).minFac ∣ card G := Nat.minFac_dvd (card G)
    simpa [hCardPow] using this
  -- Step 5.2: A prime dividing a prime power must divide the base, so `(card G).minFac ∣ p`.
  have hMinFac_dvd_p :
      (card G).minFac ∣ p :=
    hMinFacPrime.dvd_of_dvd_pow (by simpa using hMinFac_dvd_pow)
  -- Step 5.3: Since both numbers are prime, the divisibility forces equality `(card G).minFac = p`.
  have hMinFac_eq : (card G).minFac = p :=
    (Nat.prime_dvd_prime_iff_eq hMinFacPrime hp).mp hMinFac_dvd_p
  -- Step 6: Express the subgroup index in terms of the computed minimal prime factor.
  have hIndexCard : H.index = (card G).minFac := by
    -- Step 6.1.1: Substitute the computed minimal prime factor to reduce to the given index hypothesis.
    simpa [hMinFac_eq] using hH
  -- Step 7: Convert the statement to `Nat.card` and apply `Subgroup.normal_of_index_eq_minFac_card`.
  have hIndexNat : H.index = (Nat.card G).minFac := by
    simpa [Nat.card_eq_fintype_card] using hIndexCard
  exact Subgroup.normal_of_index_eq_minFac_card (G := G) (H := H) hIndexNat
