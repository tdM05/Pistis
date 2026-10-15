import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $P \triangleleft G$, $P$ a $p$-Sylow subgroup of $G$, prove that $\varphi(P) = P$ for every automorphism $\varphi$ of $G$.
-/

/-Informal Proof

Let $\phi$ be an automorphism of $G$. Let $P$ be a normal sylow p-subgroup. $\phi(P)$ is also a sylow-p subgroup. But since $P$ is normal, it is unique. Hence $\phi(P)=P$.
-/

theorem Herstein_exercise_2_11_7 {G : Type*} [Group G] {p : ℕ} (_hp : Nat.Prime p)
  {P : Sylow p G} (hP : P.Normal) :
  Subgroup.Characteristic (P : Subgroup G) := by
  classical
  -- Step 1: Upgrade the normality hypothesis to a typeclass instance for the subgroup `↑P`.
  haveI : ((P : Subgroup G).Normal) := hP
  -- Step 2: Use the characteristic criterion stated via images under automorphisms.
  refine (Subgroup.characteristic_iff_map_eq).2 ?_
  -- Step 3: Fix an arbitrary automorphism `ϕ : G ≃* G` and prove it preserves `P`.
  intro ϕ
  -- Step 3.1: Reinterpret `ϕ` as an element of `MulAut G` so that it acts on `Sylow` subgroups.
  let φ : MulAut G := ϕ
  -- Step 3.2: Consider the image of `P` under `φ` within the `MulAut` action on `Sylow` subgroups.
  let Q : Sylow p G := φ • P
  -- Step 3.3: Package the join `P ⊔ Q` into a named subgroup to avoid universe issues.
  let PQ : Subgroup G := (P : Subgroup G) ⊔ (Q : Subgroup G)
  have h_sup : IsPGroup p PQ :=
    IsPGroup.to_sup_of_normal_left
      (H := (P : Subgroup G)) (K := (Q : Subgroup G)) P.isPGroup' Q.isPGroup'
  -- Step 3.4: Maximality of `P` forces this join to equal `P`, hence `Q ≤ P`.
  have h_sup_eq : PQ = (P : Subgroup G) :=
    P.is_maximal' h_sup (by
      -- Step 3.4.1: The natural inclusion `P ≤ PQ` is used here.
      change (P : Subgroup G) ≤ (P : Subgroup G) ⊔ (Q : Subgroup G)
      exact le_sup_left)
  have h_le : (Q : Subgroup G) ≤ (P : Subgroup G) := by
    -- Step 3.4.2: Rewrite the canonical inclusion through the equality above.
    have h_lePQ : (Q : Subgroup G) ≤ PQ := by
      change (Q : Subgroup G) ≤ (P : Subgroup G) ⊔ (Q : Subgroup G)
      exact le_sup_right
    simpa [PQ, h_sup_eq] using h_lePQ
  -- Step 3.5: Since `Q` is also a Sylow subgroup, the inclusion implies `Q = P`.
  have h_eq_subgroups : (Q : Subgroup G) = (P : Subgroup G) :=
    (Q.is_maximal' P.isPGroup' h_le).symm
  -- Step 3.6: Translate this equality back to the language of subgroup images under `ϕ`.
  have h_map : (P : Subgroup G).map ϕ.toMonoidHom = (P : Subgroup G) := by
    simpa [Q, φ, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] using h_eq_subgroups
  -- Step 3.7: Conclude that `ϕ` fixes `P`, as required for characteristicity.
  simpa using h_map
