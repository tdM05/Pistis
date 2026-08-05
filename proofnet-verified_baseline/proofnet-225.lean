import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $H$ and $K$ are finite subgroups of $G$ whose orders are relatively prime then $H \cap K=1$.
-/

/-Informal Proof

Solution: Let $|H|=p$ and $|K|=q$. We saw in a previous exercise that $H \cap K$ is a subgroup of both $H$ and $K$; by Lagrange's Theorem, then, $|H \cap K|$ divides $p$ and $q$. Since $\operatorname{gcd}(p, q)=1$, then, $|H \cap K|=1$. Thus $H \cap K=1$.
-/

theorem Dummit_Foote_exercise_3_2_8 {G : Type*} [Group G] (H K : Subgroup G)
  [Fintype H] [Fintype K]
  (hHK : Nat.Coprime (card H) (card K)) :
  H ⊓ K = ⊥ := by
  classical
  -- Step 1: Use antisymmetry of `≤` on subgroups to reduce the goal to proving
  --         `H ⊓ K ≤ ⊥`, because the reverse inclusion `⊥ ≤ H ⊓ K` is automatic.
  refine le_antisymm ?_ bot_le
  -- Step 2: Fix an arbitrary group element `x` in `H ⊓ K` and prove that it must
  --         be the identity, which shows it actually belongs to `⊥`.
  intro x hx
  -- Step 2.1: Rephrase the membership goal `x ∈ ⊥` as the equation `x = 1`.
  change x = (1 : G)
  -- Step 2.2: Record separately that `x` lies in `H` and in `K`.
  have hxH : x ∈ H := by
    exact hx.1
  have hxK : x ∈ K := by
    exact hx.2
  -- Step 2.3: Apply Lagrange’s Theorem in the form "the order divides the size"
  --           to `H` so that `orderOf x ∣ card H`.
  have h_dvd_H : orderOf x ∣ card H := by
    simpa [Nat.card_eq_fintype_card] using
      (Subgroup.orderOf_dvd_natCard H hxH : orderOf x ∣ Nat.card H)
  -- Step 2.4: Repeat the same argument for `K` to obtain
  --           `orderOf x ∣ card K`.
  have h_dvd_K : orderOf x ∣ card K := by
    simpa [Nat.card_eq_fintype_card] using
      (Subgroup.orderOf_dvd_natCard K hxK : orderOf x ∣ Nat.card K)
  -- Step 2.5: Combine the two divisibility statements to deduce that
  --           `orderOf x` divides `gcd(card H, card K)`.
  have h_dvd_gcd : orderOf x ∣ Nat.gcd (card H) (card K) :=
    Nat.dvd_gcd h_dvd_H h_dvd_K
  -- Step 2.6: Use the coprimality hypothesis to rewrite that gcd as `1`, so
  --           `orderOf x ∣ 1`.
  have h_dvd_one : orderOf x ∣ 1 := by
    simpa [Nat.coprime_iff_gcd_eq_one.mp hHK] using h_dvd_gcd
  -- Step 2.7: Conclude that `orderOf x = 1`, since the only positive divisor of
  --           `1` is `1` itself.
  have hxorder : orderOf x = 1 := Nat.dvd_one.mp h_dvd_one
  -- Step 2.8: Translate `orderOf x = 1` back into `x = 1`, finishing the proof
  --           that every element of `H ⊓ K` equals the identity.
  exact (orderOf_eq_one_iff.mp hxorder)
