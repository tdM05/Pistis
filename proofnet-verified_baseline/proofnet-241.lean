import Mathlib
import Mathlib.Algebra.Group.Subgroup.Lattice

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $P$ be a normal Sylow $p$-subgroup of $G$ and let $H$ be any subgroup of $G$. Prove that $P \cap H$ is the unique Sylow $p$-subgroup of $H$.
-/

/-Informal Proof

Let $G$ be a group and $P$ is a normal $p$-Sylow subgroup of $G .|G|=p^a . m$ where $p \nmid m$. Then $|P|=p^a$. Let $H$ be a subgroup of $G$. Now if $|H|=k$ such that $p \nmid k$. Then $P \cap H=\{e\}$. There is nothing to prove in this case. Let $|H|=p^b . n$, where $b \leq a$, and $p \nmid n$. Now consider $P H$ which is a subgroup of $G$, as $P$ is normal. Now $|P H|=\frac{|P||H|}{|P \cap H|}=\frac{p^{a+b} \cdot n}{|P \cap H|}$. Now since $P H \leq G$, so $|P H|=p^a$.l, as $P \leq P H$. This forces $|P \cap H|=p^b$. So by order consideration we have $P \cap H$ is a sylow $-p$ subgroup of $H$. Now we know $P$ is unique $p$ - Sylow subgroup. Suppose $H$ has a sylow-p subgroup distinct from $P \cap H$, call it $H_1$. Now $H_1$ is a p-subgroup of $G$. So, $H_1$ is contained in some Sylow-p subgroup of $G$, call it $P_1$. Clearly $P_1$ is distinct from $P$, which is a contradiction. So $P \cap H$ is the only $p$-Sylow subgroup of $H$, and hence normal in $H$
-/

theorem Dummit_Foote_exercise_4_5_33 {G : Type*} [Group G] [Fintype G] {p : ℕ}
  (P : Sylow p G) [hP : P.Normal] (H : Subgroup G) [Fintype H] :
  (∀ R : Sylow p H, R.toSubgroup = (H ⊓ P.toSubgroup).subgroupOf H) ∧
  Nonempty (Sylow p H) := by
  classical
  -- Step 1: Record the existence of Sylow p-subgroups inside H for the second conjunct.
  have hSylowH : Nonempty (Sylow p H) := Sylow.nonempty (p := p) (G := H)
  refine ⟨?_, hSylowH⟩
  -- Step 1.1: Fix the intersection subgroup that we will repeatedly use.
  set inter : Subgroup G := H ⊓ (P : Subgroup G)
  -- Step 2: Fix an arbitrary Sylow p-subgroup R ≤ H and prove it equals H ∩ P.
  intro R
  -- Step 2.1: Embed R into G and force its image to lie inside P by maximality of P.
  -- Step 2.1.1: Name the image of R in G and remember it is still a p-group.
  set Rmap : Subgroup G := R.toSubgroup.map H.subtype with hRmap
  have hRmap_isP : IsPGroup p Rmap := (R.isPGroup').map _
  -- Step 2.1.2: Enlarge the image with P, use normality to keep a p-group, then invoke maximality.
  have h_sup_isP :
      IsPGroup p ((Rmap ⊔ (P : Subgroup G)) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right hRmap_isP P.isPGroup'
  have h_sup_eq : (Rmap ⊔ (P : Subgroup G) : Subgroup G) = P :=
    P.is_maximal' h_sup_isP (le_sup_right : (P : Subgroup G) ≤ (Rmap ⊔ (P : Subgroup G) : Subgroup G))
  have hRmap_le_P : Rmap ≤ (P : Subgroup G) := by
    have h_le_sup : Rmap ≤ (Rmap ⊔ (P : Subgroup G) : Subgroup G) := le_sup_left
    simpa [h_sup_eq] using h_le_sup
  -- Step 2.2: Pull the inclusion back to H to see that R lies in H ∩ P.
  -- Step 2.2.1: Combine containment in H and P to obtain Rmap ≤ H ∩ P inside G.
  have hRmap_le_H : Rmap ≤ H := Subgroup.map_subtype_le _
  have hRmap_le_HP :
      Rmap ≤ inter :=
    le_inf hRmap_le_H hRmap_le_P
  have hRmap_le_target :
      Rmap ≤ inter ⊓ H :=
    le_inf hRmap_le_HP hRmap_le_H
  -- Step 2.2.2: Translate the image-level inclusion to the original subgroup inside H.
  have h_target :
      (inter.subgroupOf H).map H.subtype =
        inter ⊓ H :=
    Subgroup.subgroupOf_map_subtype inter H
  have hR_le_cap :
      R.toSubgroup ≤ inter.subgroupOf H :=
    (Subgroup.map_subtype_le_map_subtype (G' := H)
          (H := R.toSubgroup)
          (K := inter.subgroupOf H)).1
      (by
        have h' : Rmap ≤ (inter.subgroupOf H).map H.subtype := by
          simpa [hRmap, h_target] using hRmap_le_target
        exact h')
  -- Step 3: Show H ∩ P is a p-group and apply the maximality of R inside H to get equality.
  -- Step 3.1: Transport the p-group structure from H ∩ P (viewed in G) to the subgroup of H.
  have h_cap_isP :
      IsPGroup p (inter.subgroupOf H) := by
    have h_inf : IsPGroup p inter :=
      (P.isPGroup').to_le (inf_le_right : inter ≤ (P : Subgroup G))
    exact
      (h_inf.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := inter)
          (K := H) inf_le_left).symm)
  -- Step 3.2: Invoke the maximality clause for R to pin down the desired equality.
  exact (R.is_maximal' h_cap_isP hR_le_cap).symm
