import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that a subgroup $H$ of $G$ is normal if and only if $[G, H] \leq H$.
-/

/-Informal Proof

$H \unlhd G$ is equivalent to $g^{-1} h g \in H, \forall g \in G, \forall h \in H$. We claim that holds if and only if $h^{-1} g^{-1} h g \in H, \forall g \in G, \forall h \in H$, i.e., $\left\{h^{-1} g^{-1} h g: h \in H, g \in G\right\} \subseteq H$. That holds by the following argument:
If $g^{-1} h g \in H, \forall g \in G, \forall h \in H$, note that $h^{-1} \in H$, so multiplying them, we also obtain an element of $H$.
On the other hand, if $h^{-1} g^{-1} h g \in H, \forall g \in G, \forall h \in H$, then
$$
h h^{-1} g^{-1} h g=g^{-1} h g \in H, \forall g \in G, \forall h \in H .
$$
Since $\left\{h^{-1} g^{-1} h g: h \in H, g \in G\right\} \subseteq H \Leftrightarrow\left\langle\left\{h^{-1} g^{-1} h g: h \in H, g \in G\right\}\right\rangle \leq H$, we've solved the exercise by definition of $[H, G]$.
-/

theorem Dummit_Foote_exercise_5_4_2 {G : Type*} [Group G] (H : Subgroup G) :
  H.Normal ↔ ⁅(⊤ : Subgroup G), H⁆ ≤ H := by
  constructor
  · -- Step 1: assume `H` is normal and aim to show `[⊤, H] ≤ H`.
    intro hH
    -- Step 1.1: register the given hypothesis as an instance for typeclass inference.
    let _ : H.Normal := hH
    -- Step 1.2: the general lemma `commutator_le_right` specialized to `H₁ = ⊤`
    --           immediately yields `[⊤, H] ≤ H`.
    --           (It uses normality of the right subgroup to bound the commutator.)
    simpa using (Subgroup.commutator_le_right (H₁ := (⊤ : Subgroup G)) (H₂ := H))
  · -- Step 2: assume `[⊤, H] ≤ H` and prove that `H` is normal.
    intro hcomm_le
    -- Step 2.1: to prove normality, we build the `Subgroup.Normal` structure explicitly.
    refine Subgroup.Normal.mk ?conj_mem
    -- Step 2.2: pick an arbitrary `n ∈ H` and an arbitrary `g : G`;
    --           we must show that the conjugate `g * n * g⁻¹` is still in `H`.
    intro n hn g
    -- Step 2.3: the commutator `[g, n]` lies in the subgroup `[⊤, H]`
    --           because `g ∈ ⊤` (trivially) and `n ∈ H`.
    have hcomm_mem : ⁅g, n⁆ ∈ ⁅(⊤ : Subgroup G), H⁆ :=
      Subgroup.commutator_mem_commutator (show g ∈ (⊤ : Subgroup G) from trivial) hn
    -- Step 2.4: using the hypothesis `[⊤, H] ≤ H`, we upgrade the previous fact
    --           to say the commutator element itself belongs to `H`.
    have hcomm_in_H : ⁅g, n⁆ ∈ H := hcomm_le hcomm_mem
    -- Step 2.5: by direct computation, the conjugate `g * n * g⁻¹`
    --           can be rewritten as the product `[g, n] * n`.
    have h_conj_as_prod : g * n * g⁻¹ = ⁅g, n⁆ * n := by
      -- Step 2.5.1: expand the commutator and cancel `n⁻¹ * n` to `1`.
      simp [commutatorElement_def, mul_assoc]
    -- Step 2.6: since `H` is a subgroup, it is closed under multiplication;
    --           combining the facts `[g, n] ∈ H` and `n ∈ H` yields `[g, n] * n ∈ H`.
    have h_mul : ⁅g, n⁆ * n ∈ H := H.mul_mem hcomm_in_H hn
    -- Step 2.7: replacing `[g, n] * n` by the conjugate expression finishes the proof.
    simpa [h_conj_as_prod] using h_mul
