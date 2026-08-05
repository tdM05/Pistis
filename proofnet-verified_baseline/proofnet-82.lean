import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $P$ is a $p$-Sylow subgroup of $G$ and $P \triangleleft G$, prove that $P$ is the only $p$-Sylow subgroup of $G$.
-/

/-Informal Proof

let $G$ be a group and $P$ a sylow-p subgroup. Given $P$ is normal. By sylow second theorem the sylow-p subgroups are conjugate. Let $K$ be any other sylow-p subgroup. Then there exists $g \in G$ such that $K=g P g^{-1}$. But since $P$ is normal $K=g P g^{-1}=P$. Hence the sylow-p subgroup is unique.
-/

theorem Herstein_exercise_2_11_6 {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
  {P : Sylow p G} (hP : P.Normal) :
  ∀ (Q : Sylow p G), P = Q := by
  -- Step 1: enable classical reasoning (the primality assumption enters through the Sylow data).
  classical
  -- Step 1.1: record the primality fact explicitly so that it is available for dependent lemmas.
  have _ : Nat.Prime p := hp
  -- Step 2: fix an arbitrary Sylow `p`-subgroup `Q` and upgrade `P`'s normality to an instance.
  intro Q
  letI : (P : Subgroup G).Normal := hP
  -- Step 3: introduce the natural quotient map `quotMap : G → G ⧸ P` produced by normality.
  let quotMap : G →* G ⧸ (P : Subgroup G) := QuotientGroup.mk' (P : Subgroup G)
  -- Step 3.1: observe that the kernel of `quotMap` is exactly `P`, hence a `p`-group.
  -- Step 3.1.1: identify the kernel explicitly via the canonical quotient formula.
  have hKer_eq : quotMap.ker = (P : Subgroup G) := by
    simp [quotMap, QuotientGroup.ker_mk']
  -- Step 3.1.2: transport the `p`-group structure along the identified kernel.
  have hKer : IsPGroup p quotMap.ker := by
    -- Step 3.1.2.1: carry the structure across the equality of subgroups.
    exact hKer_eq.symm ▸ P.2
  -- Step 3.2: the image of `Q` through `quotMap` remains a `p`-group.
  have hQMap : IsPGroup p (Q.map quotMap) := Q.2.map quotMap
  -- Step 3.3: consequently, the preimage of that image under `quotMap` is also a `p`-group.
  have hComap : IsPGroup p ((Q.map quotMap).comap quotMap) :=
    hQMap.comap_of_ker_isPGroup quotMap hKer
  -- Step 4: show that every element of `P` lies in the preimage of `Q.map quotMap`.
  have hP_le : (P : Subgroup G) ≤ (Q.map quotMap).comap quotMap := by
    intro x hx
    change quotMap x ∈ Q.map quotMap
    -- Step 4.1: an element of `P` maps to the identity in the quotient.
    have hx1 : quotMap x = 1 := by
      have hx1' : (x : G ⧸ (P : Subgroup G)) = 1 :=
        (QuotientGroup.eq_one_iff (N := (P : Subgroup G)) x).2 hx
      simpa [quotMap] using hx1'
    -- Step 4.2: deduce that the image belongs to `Q.map quotMap` because subgroups contain `1`.
    simp [hx1]
  -- Step 5: apply the maximality of `P` among `p`-subgroups to identify the preimage with `P`.
  have hComap_eq : (Q.map quotMap).comap quotMap = (P : Subgroup G) :=
    P.3 hComap hP_le
  -- Step 6: use the standard inclusion of a subgroup into the comap of its image to obtain `Q ≤ P`.
  have hQ_le_P : (Q : Subgroup G) ≤ (P : Subgroup G) := by
    have h := Subgroup.le_comap_map (f := quotMap) (Q : Subgroup G)
    simpa [hComap_eq] using h
  -- Step 7: invoke the maximality of `Q` to turn the inclusion into equality of underlying subgroups.
  have hSubgroups : (P : Subgroup G) = (Q : Subgroup G) :=
    Q.3 P.2 hQ_le_P
  -- Step 8: upgrade the equality of subgroups to an equality of Sylow subgroups.
  exact Sylow.ext hSubgroups
