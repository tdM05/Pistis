import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

If $H$ is the unique subgroup of a given order in a group $G$ prove $H$ is characteristic in $G$.
-/

/-Informal Proof

Let $G$ be group and $H$ be the unique subgroup of order $n$. Now, let $\sigma \in \operatorname{Aut}(G)$. Now Clearly $|\sigma(G)|=n$, because $\sigma$ is a one-one onto map. But then as $H$ is the only subgroup of order $n$, and because of the fact that a automorphism maps subgroups to subgroups, we have $\sigma(H)=$ $H$ for every $\sigma \in \operatorname{Aut}(G)$. Hence, $H$ is a characteristic subgroup of $G$.
-/

theorem Dummit_Foote_exercise_4_4_7 {G : Type*} [Group G] {H : Subgroup G} [Fintype H]
  (hH : ∀ (K : Subgroup G) (fK : Fintype K), card H = @card K fK → H = K) :
  H.Characteristic := by
  -- Step 0: Enable classical logic to manipulate finite cardinalities via choice-based lemmas.
  classical
  -- Step 1: Reduce the characteristic goal to proving stability of `H` under subgroup images of automorphisms.
  refine Subgroup.characteristic_iff_map_eq.mpr ?_
  -- Step 2: Fix an arbitrary automorphism `ϕ` of the group `G`.
  intro ϕ
  -- Step 2.1: Record the multiplicative equivalence between `H` and the image subgroup `H.map ϕ.toMonoidHom`.
  let hEquiv : H ≃* H.map ϕ.toMonoidHom :=
    H.equivMapOfInjective ϕ.toMonoidHom ϕ.injective
  -- Step 2.2: Transport the `Fintype` structure from `H` to `H.map ϕ.toMonoidHom` using the equivalence from Step 2.1.
  let fK : Fintype (H.map ϕ.toMonoidHom) := Fintype.ofEquiv H hEquiv.toEquiv
  -- Step 2.2.1: Register the transported `Fintype` structure as the canonical one for `H.map ϕ.toMonoidHom`.
  haveI : Fintype (H.map ϕ.toMonoidHom) := fK
  -- Step 2.3: Compute the cardinality of the image subgroup via the equivalence to `H`.
  have h_card' : card H = card (H.map ϕ.toMonoidHom) := by
    -- Step 2.3.1: Apply the cardinality equality induced by the equivalence.
    simpa using Fintype.card_congr hEquiv.toEquiv
  -- Step 3: Invoke the uniqueness hypothesis `hH` with the subgroup `H.map ϕ.toMonoidHom`.
  have h_unique : H = H.map ϕ.toMonoidHom := by
    -- Step 3.1: Supply the transported `Fintype` structure and the cardinality identity.
    simpa [fK] using
      hH (H.map ϕ.toMonoidHom) (inferInstance : Fintype (H.map ϕ.toMonoidHom)) h_card'
  -- Step 4: Flip the equality from Step 3 to express the fixed-point property required by `Characteristic`.
  exact h_unique.symm
