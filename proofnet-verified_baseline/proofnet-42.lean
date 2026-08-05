import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

noncomputable def Subgroup.relindex {G : Type*} [Group G] (H K : Subgroup G) : ℕ :=
  H.relIndex K



/-Informal Statement

Let $H \leq K \leq G$. Prove that $|G: H|=|G: K| \cdot|K: H|$ (do not assume $G$ is finite).
-/

/-Informal Proof

Proof. Let $G$ be a group and let $I$ be a nonempty set of indices, not necessarily countable. Consider the collection of subgroups $\left\{N_\alpha \mid \alpha \in I\right\}$, where $N_\alpha \unlhd G$ for each $\alpha \in I$. Let
$$
N=\bigcap_{\alpha \in I} N_\alpha .
$$
We know $N$ is a subgroup of $G$. 
For any $g \in G$ and any $n \in N$, we must have $n \in N_\alpha$ for each $\alpha$. And since $N_\alpha \unlhd G$, we have $g n g^{-1} \in N_\alpha$ for each $\alpha$. Therefore $g n g^{-1} \in N$, which shows that $g N g^{-1} \subseteq N$ for each $g \in G$. As before, this is enough to complete the proof.
-/

theorem Dummit_Foote_exercise_3_2_11 {G : Type*} [Group G] {H K : Subgroup G}
  (hHK : H ≤ K) :
  H.index = K.index * H.relindex K := by
  classical
  -- Step 1: Invoke the multiplicativity lemma `relIndex_mul_index`, which relates `H.relIndex K`, `K.index`, and `H.index`.
  have h := Subgroup.relIndex_mul_index (H := H) (K := K) hHK
  -- Step 2: Reverse the equality from Step 1 and reorder the product to match the target statement exactly.
  simpa [mul_comm] using h.symm
