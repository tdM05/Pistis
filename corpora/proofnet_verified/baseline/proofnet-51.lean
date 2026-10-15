import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $P \in \operatorname{Syl}_{p}(G)$ and $H$ is a subgroup of $G$ containing $P$ then $P \in \operatorname{Syl}_{p}(H)$.
-/

/-Informal Proof

If $P \leq H \leq G$ is a Sylow $p$-subgroup of $G$, then $p$ does not divide $[G: P]$. Now $[G: P]=[G: H][H: P]$, so that $p$ does not divide $[H: P]$; hence $P$ is a Sylow $p$-subgroup of $H$.
-/

theorem Dummit_Foote_exercise_4_5_1a {p : ℕ} {G : Type*} [Group G]
  {P : Sylow p G} (H : Subgroup G) (hH : P ≤ H) :
  IsPGroup p (P.subgroupOf H) ∧
  ∀ (Q : Subgroup H), IsPGroup p Q → (P.subgroupOf H) ≤ Q → Q = (P.subgroupOf H) := by
  classical
  -- Step 1: Define `P_H` as the Sylow subgroup of `H` obtained by restricting `P`.
  let P_H : Sylow p H := P.subtype hH
  -- Step 1.1: Record that the underlying subgroup of `P_H` is definitionally `P.subgroupOf H`.
  have hP_H_coe : (P_H : Subgroup H) = P.subgroupOf H := rfl
  -- Step 2: Extract the `p`-group property from the Sylow structure on `P_H`.
  have hPgroup : IsPGroup p (P.subgroupOf H) := by
    -- Step 2.1: Reinterpret the stored `IsPGroup` information of `P_H` through `hP_H_coe`.
    simpa [P_H, hP_H_coe] using (P_H.isPGroup')
  -- Step 3: Show that every `p`-subgroup of `H` containing `P.subgroupOf H` must coincide with it.
  have hMaximal :
      ∀ (Q : Subgroup H), IsPGroup p Q → (P.subgroupOf H) ≤ Q → Q = (P.subgroupOf H) := by
    -- Step 3.1: Introduce an arbitrary `p`-subgroup `Q` of `H` containing `P.subgroupOf H`.
    intro Q hQ hle
    -- Step 3.2: Translate the containment into the language of `P_H`.
    have hle' : (P_H : Subgroup H) ≤ Q := by
      -- Step 3.2.1: Use `hP_H_coe` to identify the two subgroups.
      simpa [P_H, hP_H_coe] using hle
    -- Step 3.3: Apply the maximality property encoded in the Sylow structure of `P_H`.
    have hEq : Q = (P_H : Subgroup H) := P_H.is_maximal' hQ hle'
    -- Step 3.4: Rewrite the obtained equality back in terms of `P.subgroupOf H`.
    simpa [P_H, hP_H_coe] using hEq
  -- Step 4: Combine the `p`-group property and the maximality property to conclude.
  exact ⟨hPgroup, hMaximal⟩
