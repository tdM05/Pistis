import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

def countably_compact (X : Type*) [TopologicalSpace X] :=
  ∀ U : ℕ → Set X,
  (∀ i, IsOpen (U i)) ∧ ((univ : Set X) ⊆ ⋃ i, U i) →
  (∃ t : Finset ℕ, (univ : Set X) ⊆ ⋃ i ∈ t, U i)

/-Informal Statement

Show that X is countably compact if and only if every nested sequence $C_1 \supset C_2 \supset \cdots$ of closed nonempty sets of X has a nonempty intersection.
-/

/-Informal Proof

We could imitate the proof of Theorem 26.9, but we prove directly each direction. First let $X$ be countable compact and let $C_1 \supset C_2 \supset \cdots$ be a nested sequence of closed nonempty sets of $X$. For each $n \in \mathbb{Z}_{+}, U_n=X \backslash C_n$ is open in $X$. Then $\left\{U_n\right\}_{n \in \mathbb{Z}_{+}}$is a countable collection of open sets with no finite subcollection covering $X$, for if $U_{i_1} \cup \cdots \cup U_{1_n}$ covers $X$, then $C_{i_1} \cap \cdots \cap C_{i_n}$ is empty, contrary to the assumption. Hence $\left\{U_n\right\}_{n \in \mathbb{Z}_{+}}$does not cover $X$, so there exist $x \in X \backslash \bigcup_{n \in \mathbb{Z}_{+}} U_n=\bigcap_{n \in Z_{+}}\left(X \backslash U_n\right)=\bigcap_{n \in Z_{+}} C_n$.

Conversely, assume that every nested sequence $C_1 \supset C_2 \supset \cdots$ of closed non-empty sets of $X$ has a non-empty intersection and let $\left\{U_n\right\}_{n \in \mathbb{Z}_{+}}$be a countable open covering of $X$. For each $n$, let $V_n=U_1 \cup \cdots \cup U_n$ and $C_n=X \backslash V_n$. Suppose that no finite subcollection of $\left\{U_n\right\}_{n \in \mathbb{Z}_{+}}$covers $X$. Then each $C_n$ is non-empty, so $C_1 \supset C_2 \supset \cdots$ is a nested sequence of non-empty closed sets and $\bigcap_{n \in \mathbb{Z}_{+}} C_n$ is non-empty by assumption. Then there exists $x \in \bigcap_{n \in \mathbb{Z}_{+}} C_n$, so that $x \notin V_n$ for all $n$, contradicting the fact that $\left\{U_n\right\}_{n \in \mathbb{Z}_{+}}$covers $X$. It follows that there exists $N \in \mathbb{Z}_{+}$such that $C_N=\emptyset$, so that $X=V_N$ and hence some finite subcollection of $\left\{U_n\right\}_{n \in \mathbb{Z}_{+}}$covers $X$. We deduce that $X$ is countable compact.
-/

theorem Munkres_exercise_28_5
  (X : Type*) [TopologicalSpace X] :
  countably_compact X ↔ ∀ (C : ℕ → Set X), (∀ n, IsClosed (C n)) ∧
  (∀ n, C n ≠ ∅) ∧ (∀ n, C (n + 1) ⊆ C n) → ∃ x, ∀ n, x ∈ C n := by
  classical
  -- Step 0: We work classically so that we can extract witnesses from nonempty sets.
  constructor
  · -- Step 1: Assume X is countably compact and fix a nested family of closed sets satisfying the premises.
    intro hcc C hCdata
    rcases hCdata with ⟨hclosed, hnonempty, hnested⟩
    -- Step 1.2: Establish that the family C is antitone (descending with respect to ℕ).
    have hmonoC : Antitone C := by
      -- Step 1.2.1: To show antitonicity, compare indices i ≤ j and peel off the difference.
      intro i j hij
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
      -- Step 1.2.2: Express j as i + k and prove the inclusion by induction on k.
      subst hk
      -- Step 1.2.2.1: Define an auxiliary lemma: repeatedly applying hnested keeps shrinking the sets.
      have hdesc : ∀ n, C (i + n) ⊆ C i := by
        intro n
        induction n with
        | zero =>
            simp
        | succ n ih =>
            have hstep : C (i + n + 1) ⊆ C (i + n) := by
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hnested (i + n)
            -- Step 1.2.2.1.1: Compose the current step with the induction hypothesis.
            have := hstep.trans ih
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
      -- Step 1.2.2.2: Evaluate the auxiliary lemma at the required difference k.
      simpa using hdesc k
    -- Step 1.3: Argue by contradiction that the intersection of all C n is nonempty.
    by_contra hEmpty
    -- Step 1.3.1: Convert the negated conclusion into the statement that complements cover X.
    have hcover : (Set.univ : Set X) ⊆ ⋃ n, (C n)ᶜ := by
      -- Step 1.3.1.1: For each point x, produce an index witnessing its exclusion from some C n.
      intro x hx
      have hxneg : ¬ ∀ n, x ∈ C n := (not_exists.mp hEmpty) x
      obtain ⟨n, hxn⟩ := not_forall.mp hxneg
      -- Step 1.3.1.2: Translate “x ∉ C n” into membership in the complement (C n)ᶜ.
      exact Set.mem_iUnion.mpr ⟨n, by simpa using hxn⟩
    -- Step 1.4: Apply countable compactness to the open cover given by the complements.
    have hopen : ∀ n, IsOpen ((C n)ᶜ) := fun n => (hclosed n).isOpen_compl
    obtain ⟨t, hfin⟩ := hcc (fun n => (C n)ᶜ) ⟨hopen, hcover⟩
    -- Step 1.5: Derive a contradiction by studying the finite union of complements.
    -- Step 1.5.1: Show that the finite index set t is nonempty; otherwise the union would be empty.
    have htne : t.Nonempty := by
      -- Step 1.5.1.1: Choose a point in C 0 using the nonemptiness hypothesis.
      obtain ⟨x₀, hx₀⟩ :=
        (Set.nonempty_iff_ne_empty).mpr (hnonempty 0)
      -- Step 1.5.1.2: If t were empty, x₀ could not lie in the empty union, contradicting the finite cover.
      classical
      by_contra hte
      have hxmem : x₀ ∈ ⋃ i ∈ t, (C i)ᶜ := hfin (by trivial)
      obtain ⟨i, hxmem⟩ := Set.mem_iUnion.mp hxmem
      obtain ⟨hi, _⟩ := Set.mem_iUnion.mp hxmem
      exact hte ⟨i, hi⟩
    -- Step 1.5.2: Select the maximal index inside t to exploit the nested structure.
    classical
    let m := t.max' htne
    have hm_mem : m ∈ t := by
      -- Step 1.5.2.1: The maximal element returned by max' truly belongs to the index set.
      simpa [m] using (Finset.max'_mem (s := t) htne)
    -- Step 1.5.3: Simplify the finite union by showing it coincides with the complement at the maximal index.
    have hUnion_eq : (⋃ i ∈ t, (C i)ᶜ) = (C m)ᶜ := by
      -- Step 1.5.3.1: First inclusion – every term in the union sits inside (C m)ᶜ because of monotonicity.
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hi_mem, hxComp⟩ := Set.mem_iUnion.mp hi
        have hi_le : i ≤ m := by
          -- Step 1.5.3.1.1: Use maximality to compare the chosen index with m.
          simpa [m] using (Finset.le_max' (s := t) (x := i) hi_mem)
        -- Step 1.5.3.1.2: Translate membership in the complement into “not belonging” statements.
        have hnotCi : ¬ x ∈ C i := by simpa using hxComp
        -- Step 1.5.3.1.3: Carry the point up the chain C m ⊆ C i to obtain the desired contradiction.
        have hsubset : C m ⊆ C i := hmonoC hi_le
        have hnotCm : ¬ x ∈ C m := by
          intro hxm
          exact hnotCi (hsubset hxm)
        exact hnotCm
      · -- Step 1.5.3.2: Second inclusion – since m lies in t, its complement is part of the union.
        intro x hx
        refine Set.mem_iUnion.mpr ?_
        refine ⟨m, Set.mem_iUnion.mpr ?_⟩
        exact ⟨hm_mem, hx⟩
    -- Step 1.5.4: The finite cover forces every point to lie in (C m)ᶜ, so C m must be empty.
    have hsubsetCm : (Set.univ : Set X) ⊆ (C m)ᶜ := by
      simpa [hUnion_eq] using hfin
    have hCm_empty : C m = (∅ : Set X) := by
      -- Step 1.5.4.1: Show that every point of C m leads to a contradiction with the preceding inclusion.
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have : x ∈ (C m)ᶜ := hsubsetCm (by trivial)
      exact this hx
    -- Step 1.5.5: Contradict the assumption that each C n is nonempty.
    exact (hnonempty m) hCm_empty
  · -- Step 2: Assume every nested sequence of closed nonempty sets intersects; prove countable compactness.
    intro hNested U hUdata
    rcases hUdata with ⟨hopen, hcover⟩
    -- Step 2.2: Argue by contradiction: assume no finite subcollection covers X.
    classical
    by_contra hNoFinite
    -- Step 2.3: From the negated existence, deduce that every finite subset fails to cover X.
    have hnofin :
        ∀ t : Finset ℕ, ¬ (Set.univ : Set X) ⊆ ⋃ i ∈ t, U i :=
      not_exists.mp hNoFinite
    -- Step 2.4: Define the auxiliary unions V n and their complements Cseq n.
    let V : ℕ → Set X := fun n => ⋃ i ∈ Finset.range (n + 1), U i
    let Cseq : ℕ → Set X := fun n => (V n)ᶜ
    -- Step 2.5: Show that each Cseq n is closed, nonempty, and the sequence is nested.
    have hopenFinset :
        ∀ s : Finset ℕ, IsOpen (⋃ i ∈ s, U i) := by
      -- Step 2.5.0: Finite unions of the U i are open by induction on the index set.
      intro s
      refine Finset.induction_on s ?base ?step
      · -- Step 2.5.0.1: The union over the empty set is ∅, which is open.
        simp
      · -- Step 2.5.0.2: Adding one more index preserves openness via stability under finite unions.
        intro a s ha hs
        have : IsOpen (U a ∪ ⋃ i ∈ s, U i) := (hopen a).union hs
        simpa [Finset.mem_insert, Set.union_comm, Set.union_left_comm, Set.union_assoc]
    have hC_closed : ∀ n, IsClosed (Cseq n) := by
      -- Step 2.5.1: Finite unions of open sets remain open; complements are therefore closed.
      intro n
      have hopenUnion : IsOpen (V n) := by
        simpa [V] using hopenFinset (Finset.range (n + 1))
      simpa [Cseq] using hopenUnion.isClosed_compl
    have hC_nonempty : ∀ n, Cseq n ≠ (∅ : Set X) := by
      -- Step 2.5.2: For each n, the finite range (n + 1) fails to cover, giving a point in the complement.
      intro n
      have hnot := hnofin (Finset.range (n + 1))
      -- Step 2.5.2.1: Use Set.not_subset to extract a witness outside the finite union.
      obtain ⟨x, _, hxnot⟩ := Set.not_subset.mp hnot
      -- Step 2.5.2.2: The witness lives in the complement, showing Cseq n is nonempty.
      have hxCseq : (Cseq n).Nonempty := ⟨x, by simpa [Cseq, V] using hxnot⟩
      exact (Set.nonempty_iff_ne_empty).mp hxCseq
    have hC_nested : ∀ n, Cseq (n + 1) ⊆ Cseq n := by
      -- Step 2.5.3: The unions V n are increasing, so their complements are decreasing.
      intro n x hx
      -- Step 2.5.3.1: Expand the statement “x ∈ V (n + 1)” to membership in a larger finite union.
      have hsubset : V n ⊆ V (n + 1) := by
        intro y hy
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
        obtain ⟨hi_mem, hyU⟩ := Set.mem_iUnion.mp hi
        refine Set.mem_iUnion.mpr ?_
        refine ⟨i, Set.mem_iUnion.mpr ?_⟩
        have hi_lt : i < n + 1 := by simpa [Finset.mem_range] using hi_mem
        refine ⟨by simp [Finset.mem_range]; omega, hyU⟩
      -- Step 2.5.3.2: Translate membership in complements to show the required inclusion.
      refine ?_
      -- Step 2.5.3.3: Specialise the inclusion to x to transfer the contradiction.
      intro hxIn
      exact hx (hsubset hxIn)
    -- Step 2.6: Apply the hypothesis to the constructed descending family.
    obtain ⟨x, hxC⟩ := hNested Cseq ⟨hC_closed, hC_nonempty, hC_nested⟩
    -- Step 2.7: Derive that x avoids every set U n, contradicting the original cover.
    have hx_not_cover : x ∈ ⋂ n, (U n)ᶜ := by
      -- Step 2.7.1: Each membership hxC n says x lies in (V n)ᶜ, hence outside all U i for i ≤ n.
      refine Set.mem_iInter.mpr ?_
      intro n
      have hUnsubset : U n ⊆ V n := by
        intro y hy
        refine Set.mem_iUnion.mpr ?_
        refine ⟨n, Set.mem_iUnion.mpr ?_⟩
        have hn_lt : n < n + 1 := Nat.lt_succ_self _
        refine ⟨by simp [Finset.mem_range], hy⟩
      -- Step 2.7.1.1: Use the inclusion U n ⊆ V n to pass from “x ∉ V n” to “x ∉ U n”.
      have hxnotV : x ∈ (V n)ᶜ := hxC n
      refine ?_
      -- Step 2.7.1.2: If x were in U n, then hUnsubset would place it inside V n, violating hxnotV.
      intro hxUn
      exact hxnotV (hUnsubset hxUn)
    -- Step 2.8: Conclude that x is outside the global union, violating the covering property.
    have hxnotUnion : x ∉ ⋃ n, U n := by
      -- Step 2.8.1: If x belonged to some U n, the previous step would forbid it.
      intro hxUnion
      obtain ⟨n, hxUn⟩ := Set.mem_iUnion.mp hxUnion
      have hxnot := (Set.mem_iInter.mp hx_not_cover n)
      exact hxnot hxUn
    -- Step 2.9: Contradict the fact that the open family covers X, finishing the argument.
    have hx_univ : x ∈ (Set.univ : Set X) := by trivial
    have : x ∈ ⋃ n, U n := hcover hx_univ
    exact hxnotUnion this
