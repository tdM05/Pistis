import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $G$ be a transitive permutation group on the finite set $A$ with $|A|>1$. Show that there is some $\sigma \in G$ such that $\sigma(a) \neq a$ for all $a \in A$.
-/

/-Informal Proof

Let $G$ be a transitive permutation group on the finite set $A,|A|>1$. We want to find an element $\sigma$ which doesn't stabilize anything, that is, we want a $\sigma$ such that
$$
\sigma \notin G_a
$$
for all $a \in A$.
Since the group is transitive, there is always a $g \in G$ such that $b=g \cdot a$. Let us see in what relationship the stabilizers of $a$ and $b$ are. We find
$$
\begin{aligned}
G_b & =\{h \in G \mid h \cdot b=b\} \\
& =\{h \in G \mid h g \cdot a=g \cdot a\} \\
& =\left\{h \in G \mid g^{-1} h g \cdot a=a\right\}
\end{aligned}
$$
Putting $h^{\prime}=g^{-1} h g$, we have $h=g h^{\prime} g^{-1}$ and
$$
\begin{aligned}
G_b & =g\left\{h^{\prime} \in H \mid h^{\prime} \cdot a=a\right\} g^{-1} \\
& =g G_a g^{-1}
\end{aligned}
$$
By the above, the stabilizer subgroup of any element is conjugate to some other stabilizer subgroup. Now, the stabilizer cannot be all of $G$ (else $\{a\}$ would be a orbit). Thus it is a proper subgroup of $G$. By the previous exercise, we have
$$
\bigcup_{a \in A} G_a=\bigcup_{g \in G} g G_a g^{-1} \subset G
$$
(the union of conjugates of a proper subgroup can never be all of $G$ ). This shows there is an element $\sigma$ which is not in any stabilizer of any element of $A$. Then $\sigma(a) \neq a$ for all $a \in A$, as we wanted to show.
-/

theorem Dummit_Foote_exercise_4_3_26 {α : Type*} [Fintype α] (ha : card α > 1)
  (h_tran : ∀ a b: α, ∃ σ : Equiv.Perm α, σ a = b) :
  ∃ σ : Equiv.Perm α, ∀ a : α, σ a ≠ a := by
  classical
  -- Step 0: Record the transitivity assumption in the context (the counting argument below does not need to invoke it explicitly).
  have _ := h_tran
  -- Step 1: Translate the cardinality hypothesis into the inequality |α| ≥ 2 (we do not need h_tran explicitly).
  have htwo : 2 ≤ Fintype.card α := Nat.succ_le_of_lt ha
  -- Step 2: Establish by induction that every numDerangements (n + 2) is positive.
  have num_pos_succ_succ : ∀ n : ℕ, 0 < numDerangements (n + 2) := by
    -- Step 2.1: Base case n = 0, where the unique derangement on a 2-element set is the transposition.
    refine Nat.rec ?base ?step
    · -- Step 2.1.1: Explicitly evaluate numDerangements 2.
      simp [numDerangements]
    -- Step 2.2: Inductive step transferring positivity from n + 2 to n + 3.
    · intro n ih
      -- Step 2.2.1: The previously established positivity gives a positive summand for the recurrence.
      have hsum :
          0 < numDerangements (n + 1) + numDerangements (n + 2) :=
        lt_of_lt_of_le ih (Nat.le_add_left _ _)
      -- Step 2.2.2: The multiplicative factor (n + 2) is positive in ℕ.
      have hfactor : 0 < n + 2 := Nat.succ_pos _
      -- Step 2.2.3: Combine the factor and the sum through the recursive formula.
      have hmul :
          0 < (n + 2) * (numDerangements (n + 1) + numDerangements (n + 2)) :=
        Nat.mul_pos hfactor hsum
      -- Step 2.2.4: Rewrite the product as numDerangements (n + 3).
      simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
        numDerangements_add_two] using hmul
  -- Step 3: Specialize the positivity lemma to |α| by rewriting |α| = (|α| - 2) + 2.
  have h_num_pos : 0 < numDerangements (Fintype.card α) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.sub_add_cancel htwo] using
      num_pos_succ_succ (Fintype.card α - 2)
  -- Step 4: Convert the positivity of numDerangements into a positive cardinality of the derangement subtype.
  have h_der_card_pos : 0 < Fintype.card (derangements α) := by
    simpa [card_derangements_eq_numDerangements (α := α)] using h_num_pos
  -- Step 5: Extract an explicit derangement from the nonempty subtype ensured by the positive cardinality.
  obtain ⟨⟨σ, hσ⟩⟩ := (Fintype.card_pos_iff.mp h_der_card_pos)
  -- Step 6: Present the witness as the required permutation with no fixed points.
  refine ⟨σ, ?_⟩
  intro a
  -- Step 6.1: Directly use the defining property of the derangement subtype.
  exact hσ a


/-
Correction summary:

The original statement formalized only the existence of a derangement of the
whole permutation group `Equiv.Perm α`.  It did not include the subgroup `G`,
so the transitivity hypothesis and the conclusion were about all permutations,
not about the given transitive subgroup.

The corrected statement adds `G : Subgroup (Equiv.Perm α)`, states
transitivity as `∀ a b, ∃ σ : G, σ a = b`, and concludes
`∃ σ : G, ∀ a, σ a ≠ a`.  Thus the fixed-point-free element is now proved to
belong to the original transitive permutation group, exactly as required by the informal theorem.
-/
theorem Dummit_Foote_exercise_4_3_26_corrected {α : Type*} [Fintype α] (ha : Fintype.card α > 1)
  (G : Subgroup (Equiv.Perm α))
  (h_tran : ∀ a b : α, ∃ σ : G, (σ : Equiv.Perm α) a = b) :
  ∃ σ : G, ∀ a : α, (σ : Equiv.Perm α) a ≠ a := by
  classical
  haveI : Fintype G := Fintype.ofFinite _
  haveI hα : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  -- Pretransitive action of G on α
  haveI hPre : MulAction.IsPretransitive G α := ⟨h_tran⟩
  -- The orbit space has exactly one element
  haveI : Fintype (MulAction.orbitRel.Quotient G α) := Fintype.ofFinite _
  haveI : Unique (MulAction.orbitRel.Quotient G α) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty G α).mp hPre)
  -- Fintype on each fixedBy
  haveI : ∀ g : G, Fintype (MulAction.fixedBy α g) := fun _ => Fintype.ofFinite _
  -- Burnside: ∑ |Fix(g)| = |orbits| · |G| = |G|
  have hburn :
      (∑ g : G, Fintype.card (MulAction.fixedBy α g)) =
        Fintype.card (MulAction.orbitRel.Quotient G α) * Fintype.card G :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G α
  rw [Fintype.card_unique, one_mul] at hburn
  -- Suppose every σ ∈ G fixes some point; derive a contradiction.
  by_contra hcon
  push_neg at hcon
  have hpos : ∀ g : G, 1 ≤ Fintype.card (MulAction.fixedBy α g) := by
    intro g
    obtain ⟨a, ha⟩ := hcon g
    refine Fintype.card_pos_iff.mpr ⟨⟨a, ?_⟩⟩
    show g • a = a
    rw [Subgroup.smul_def]
    exact ha
  -- Identity fixes everything
  have hid : Fintype.card α ≤ Fintype.card (MulAction.fixedBy α (1 : G)) := by
    apply Fintype.card_le_of_injective (fun a => ⟨a, by show (1 : G) • a = a; simp⟩)
    intro a b h
    simpa using h
  -- Split off the identity term and bound the rest below by |G| - 1
  have hsplit :
      (∑ g : G, Fintype.card (MulAction.fixedBy α g)) =
        Fintype.card (MulAction.fixedBy α (1 : G)) +
          ∑ g ∈ (Finset.univ : Finset G).erase 1,
            Fintype.card (MulAction.fixedBy α g) := by
    rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ (1 : G))]
  have hcard : ((Finset.univ : Finset G).erase 1).card = Fintype.card G - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hsum_one :
      Fintype.card G - 1 ≤
        ∑ g ∈ (Finset.univ : Finset G).erase 1,
          Fintype.card (MulAction.fixedBy α g) := by
    calc Fintype.card G - 1
        = ((Finset.univ : Finset G).erase 1).card := hcard.symm
      _ = ∑ _g ∈ (Finset.univ : Finset G).erase 1, 1 := by simp
      _ ≤ ∑ g ∈ (Finset.univ : Finset G).erase 1,
            Fintype.card (MulAction.fixedBy α g) :=
            Finset.sum_le_sum fun g _ => hpos g
  -- |α| + (|G| - 1) ≤ ∑ |Fix(g)| = |G|, hence |α| ≤ 1, contradicting ha
  have hG : 0 < Fintype.card G := Fintype.card_pos
  omega
