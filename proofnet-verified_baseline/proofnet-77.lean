import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $G$ is a nonabelian group of order 6, prove that $G \simeq S_3$.
-/

/-Informal Proof

Suppose $G$ is a non-abelian group of order 6 . We need to prove that $G \cong S_3$. Since $G$ is non-abelian, we conclude that there is no element of order 6. Now all the nonidentity element has order either 2 or 3 . All elements cannot be order 3 .This is because except the identity elements there are 5 elements, but order 3 elements occur in pair, that is $a, a^2$, both have order 3 , and $a \neq a^2$. So, this is a contradiction, as there are only 5 elements. So, there must be an element of order 2 . All elements of order 2 will imply that $G$ is abelian, hence there is also element of order 3 . Let $a$ be an element of order 2 , and $b$ be an element of order 3 . So we have $e, a, b, b^2$, already 4 elements. Now $a b \neq e, b, b^2$. So $a b$ is another element distinct from the ones already constructed. $a b^2 \neq e, b, a b, b^2, a$. So, we have got another element distinct from the other. So, now $ G=\left\{e, a, b, b^2, a b, a b^2\right\}$. Also, ba must be equal to one of these elements. But $b a \neq e, a, b, b^2$. Also if $b a=a b$, the group will become abelian. so $b a=a b^2$. So what we finally get is $G=\left\langle a, b \mid a^2=e=b^3, b a=a b^2\right\rangle$. Hence $G \cong S_3$.
-/

theorem Herstein_exercise_2_5_37 (G : Type*) [Group G] [Fintype G]
  (hG : card G = 6) (hG' : IsEmpty (CommGroup G)) :
  Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  classical
  /-
  Step 1: Rewrite `card G = 6` as a statement about `Fintype.card G`.

  Here `card` is notation for `Fintype.card`, so we can convert `hG` directly
  into an equality on `Fintype.card G`. This will be the only place where we
  use the actual size of `G`.
  -/
  have hCardG : Fintype.card G = 6 := by
    -- Step 1.1: Interpret `hG` in terms of `Fintype.card`.
    simpa using hG

  /-
  Step 2: Fix a concrete finite commutative group of order `6`.

  Let `β := Multiplicative (ZMod 6)`:
  * `ZMod 6` is the ring of integers modulo `6`; its additive structure is a
    finite abelian group of cardinality `6`.
  * `Multiplicative` turns this additive structure into a multiplicative one,
    and mathlib provides a `CommGroup` instance on `Multiplicative (ZMod 6)`.

  In this step, we:
  * (Step 2.1) Define the auxiliary type `β`;
  * (Step 2.2) Record that `β` has exactly `6` elements.
  -/
  let β := Multiplicative (ZMod 6)

  -- Step 2.2: Use the standard cardinality result for `ZMod` and the fact that
  -- `Multiplicative` is just a type tag, so it preserves the finite cardinality.
  have hCardβ : Fintype.card β = 6 := by
    -- `ZMod.card` states `Fintype.card (ZMod n) = n`. The `simp` step rewrites
    -- along the definition of `β` and the `Fintype` instance for `Multiplicative`.
    simp [β]

  /-
  Step 3: Build an explicit bijection `e : G ≃ β` from the equality of cardinalities.

  Since both `G` and `β` have cardinality `6`, `Fintype.equivOfCardEq` constructs
  a type-theoretic equivalence between them.
  -/
  have hCardEq : Fintype.card G = Fintype.card β := by
    -- Step 3.1: Both sides are equal to `6`, so they are equal to each other.
    simpa [hCardβ] using hCardG

  -- Step 3.2: Extract the equivalence from the equality of cardinalities.
  let e : G ≃ β := Fintype.equivOfCardEq hCardEq

  /-
  Step 4: Transport the commutative group structure from `β` to `G`.

  The equivalence `e : G ≃ β` allows us to *pull back* any `CommGroup` structure
  from `β` to `G`. Mathlib provides this transport as

      `(e.symm).commGroup : CommGroup G`

  where we read the commutative group structure from `β` and view `G` as the
  same group with elements renamed by `e`.

  This yields a specific inhabitant of the type `CommGroup G`.
  -/
  have instCG : CommGroup G := e.commGroup

  /-
  Step 5: Derive a contradiction from `IsEmpty (CommGroup G)`.

  The hypothesis `hG' : IsEmpty (CommGroup G)` asserts that there are *no*
  inhabitants of the type `CommGroup G`. But in Step 4 we just produced one,
  namely `instCG`. Applying the eliminator for `IsEmpty` to this inhabitant
  yields a proof of `False`.
  -/
  have hFalse : False := hG'.elim instCG

  /-
  Step 6: Conclude the desired statement from the contradiction.

  From `False` we can derive any proposition, including the existence of a
  multiplicative group isomorphism `G ≃* Equiv.Perm (Fin 3)`. We use
  `False.elim` to obtain a term of the requested type.
  -/
  exact False.elim hFalse


/-
Corrected version of the statement.

The original statement uses `IsEmpty (CommGroup G)` to express "G is non-abelian".
This is not equivalent to "the group `G` is non-abelian": `IsEmpty (CommGroup G)`
asserts that there is no commutative group structure on the type `G` at all, but
since any finite group of order 6 has a commutative group structure on its
underlying type (e.g., transported from `ZMod 6`), this hypothesis is actually
contradictory whenever `Fintype.card G = 6`. The original "proof" exploits this
to derive `False` from the hypothesis, rather than proving the genuine
mathematical statement.

The corrected statement expresses non-abelian-ness using the *existing* group
structure on `G`: there exist elements `a, b : G` with `a * b ≠ b * a`.
-/
theorem Herstein_exercise_2_5_37_corrected (G : Type*) [Group G] [Fintype G]
  (hG : card G = 6) (hG' : ∃ a b : G, a * b ≠ b * a) :
  Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  classical
  have hCardG : Fintype.card G = 6 := by simpa using hG
  have hNatCardG : Nat.card G = 6 := by
    rw [Nat.card_eq_fintype_card]; exact hCardG
  /-
  Step 1: By Cauchy's theorem, find elements `a` and `b` of `G` with
  `orderOf a = 2` and `orderOf b = 3`.
  -/
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2dvd : (2 : ℕ) ∣ Fintype.card G := by rw [hCardG]; decide
  have h3dvd : (3 : ℕ) ∣ Fintype.card G := by rw [hCardG]; decide
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card 2 h2dvd
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card 3 h3dvd
  /-
  Step 2: Define `H = ⟨a⟩` and `K = ⟨b⟩`, the cyclic subgroups generated
  by `a` and `b`. They have cardinalities 2 and 3 respectively.
  -/
  set H : Subgroup G := Subgroup.zpowers a with hH_def
  set K : Subgroup G := Subgroup.zpowers b with hK_def
  have hCardH : Fintype.card H = 2 := by
    show Fintype.card (Subgroup.zpowers a) = 2
    rw [Fintype.card_zpowers, ha]
  have hCardK : Fintype.card K = 3 := by
    show Fintype.card (Subgroup.zpowers b) = 3
    rw [Fintype.card_zpowers, hb]
  have hNatCardH : Nat.card H = 2 := by
    rw [Nat.card_eq_fintype_card]; exact hCardH
  have hNatCardK : Nat.card K = 3 := by
    rw [Nat.card_eq_fintype_card]; exact hCardK
  /-
  Step 3: `H` and `K` are disjoint as subgroups: any common element has order
  dividing both `2` and `3`, hence order `1`, hence equals `1`.
  -/
  have hDisj : Disjoint H K := by
    rw [Subgroup.disjoint_def]
    intro x hxH hxK
    have hx2 : orderOf x ∣ 2 := by
      have h := orderOf_dvd_card (x := (⟨x, hxH⟩ : H))
      rwa [Subgroup.orderOf_mk, hCardH] at h
    have hx3 : orderOf x ∣ 3 := by
      have h := orderOf_dvd_card (x := (⟨x, hxK⟩ : K))
      rwa [Subgroup.orderOf_mk, hCardK] at h
    have h1 : orderOf x = 1 := by
      have hgcd : orderOf x ∣ Nat.gcd 2 3 := Nat.dvd_gcd hx2 hx3
      simpa using hgcd
    exact orderOf_eq_one_iff.mp h1
  /-
  Step 4: `K` has index 2 in `G`, hence `K` is normal.
  -/
  have hKindex2 : K.index = 2 := by
    have hLag := K.card_mul_index
    rw [hNatCardK, hNatCardG] at hLag
    omega
  haveI hKnormal : K.Normal := Subgroup.normal_of_index_eq_two hKindex2
  /-
  Step 5: `H` is *not* normal in `G`. Otherwise, both `H` and `K` would be
  normal with trivial intersection, hence elementwise commute. In particular
  `a * b = b * a`. Then `orderOf (a * b) = 6 = card G`, so `G` is cyclic and
  hence commutative, contradicting `hG'`.
  -/
  have hHnotNormal : ¬ H.Normal := by
    intro hHnormal
    have hab_comm : Commute a b :=
      Subgroup.commute_of_normal_of_disjoint H K hHnormal hKnormal hDisj a b
        (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers b)
    have hcoprime : (orderOf a).Coprime (orderOf b) := by
      rw [ha, hb]; decide
    have hord_ab : orderOf (a * b) = 6 := by
      rw [hab_comm.orderOf_mul_eq_mul_orderOf_of_coprime hcoprime, ha, hb]
    have hcyc : IsCyclic G :=
      isCyclic_of_orderOf_eq_card (a * b) (by rw [hord_ab, hNatCardG])
    have hcomm := (IsCyclic.commutative (α := G)).comm
    obtain ⟨x, y, hxy⟩ := hG'
    exact hxy (hcomm x y)
  /-
  Step 6: `H.normalCore = ⊥`. Indeed, `H.normalCore.subgroupOf H` is a subgroup
  of the prime-order group `H`, so it is either `⊥` or `⊤`. The `⊤` case forces
  `H.normalCore = H`, which would make `H` normal — contradicting Step 5.
  Hence it is `⊥`, i.e. `H.normalCore` is disjoint from `H`. Combined with
  `H.normalCore ≤ H`, this gives `H.normalCore = ⊥`.
  -/
  have hNormCore : H.normalCore = ⊥ := by
    haveI : Fact (Nat.card H).Prime := ⟨hNatCardH ▸ Nat.prime_two⟩
    rcases (H.normalCore.subgroupOf H).eq_bot_or_eq_top_of_prime_card with hbot | htop
    · rw [Subgroup.subgroupOf_eq_bot] at hbot
      have hsub : H.normalCore ⊓ H = H.normalCore := inf_of_le_left H.normalCore_le
      have : H.normalCore ⊓ H ≤ ⊥ := hbot.le_bot
      rw [hsub] at this
      exact le_bot_iff.mp this
    · rw [Subgroup.subgroupOf_eq_top] at htop
      have h_eq : H.normalCore = H := le_antisymm H.normalCore_le htop
      exact absurd (h_eq ▸ H.normalCore_normal) hHnotNormal
  /-
  Step 7: The action of `G` on `G ⧸ H` by left multiplication gives a group
  homomorphism `φ : G →* Equiv.Perm (G ⧸ H)`. Its kernel is `H.normalCore`,
  which is `⊥` by Step 6, so `φ` is injective.
  -/
  set φ : G →* Equiv.Perm (G ⧸ H) := MulAction.toPermHom G (G ⧸ H) with hφ_def
  have hker : φ.ker = ⊥ := by
    rw [hφ_def, ← Subgroup.normalCore_eq_ker]
    exact hNormCore
  have hφ_inj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  /-
  Step 8: `Fintype.card (G ⧸ H) = 3` (Lagrange's identity), and therefore
  `Fintype.card (Equiv.Perm (G ⧸ H)) = 3! = 6 = Fintype.card G`. Combined
  with injectivity from Step 7, `φ` is bijective.
  -/
  have hCardQuot : Fintype.card (G ⧸ H) = 3 := by
    have hLag : Nat.card G = Nat.card (G ⧸ H) * Nat.card H :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup H
    rw [hNatCardG, hNatCardH, Nat.card_eq_fintype_card] at hLag
    omega
  have hCardPerm : Fintype.card (Equiv.Perm (G ⧸ H)) = 6 := by
    rw [Fintype.card_perm, hCardQuot]; rfl
  have hφ_bij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hφ_inj, ?_⟩
    rw [hCardG, hCardPerm]
  /-
  Step 9: Promote the bijective hom to a `MulEquiv`, and compose with the
  multiplicative equivalence `Equiv.Perm (G ⧸ H) ≃* Equiv.Perm (Fin 3)` induced
  by the bijection `(G ⧸ H) ≃ Fin 3` (from equal cardinalities).
  -/
  let ψ : G ≃* Equiv.Perm (G ⧸ H) := MulEquiv.ofBijective φ hφ_bij
  let e : G ⧸ H ≃ Fin 3 := Fintype.equivFinOfCardEq hCardQuot
  let χ : Equiv.Perm (G ⧸ H) ≃* Equiv.Perm (Fin 3) := Equiv.permCongrHom e
  exact ⟨ψ.trans χ⟩
