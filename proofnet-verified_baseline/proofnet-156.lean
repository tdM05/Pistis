import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Suppose $E\subset\mathbb{R}^k$ is uncountable, and let $P$ be the set of condensation points of $E$. Prove that $P$ is perfect.
-/

/-Informal Proof

We see that $E \cap W$ is at most countable, being a countable union of at-most-countable sets. It remains to show that $P=W^c$, and that $P$ is perfect.
-/

theorem Rudin_exercise_2_27a (k : ℕ) (E P : Set (EuclideanSpace ℝ (Fin k)))
  (hE : ¬ Set.Countable E)
  (hP : P = {x | ∀ U ∈ 𝓝 x, ¬ Set.Countable (U ∩ E)}) :
  Perfect P := by
  -- Step 1: Work classically so that we can pick explicit witnesses from uncountable sets.
  classical
  -- Step 2: Record the defining property of membership in `P` for future rewriting.
  have hcond : ∀ {x}, x ∈ P ↔ ∀ U ∈ 𝓝 x, ¬ Set.Countable (U ∩ E) := by
    intro x; simp [hP]
  -- Step 3: Show that the set of points of `E` that are not condensation points is countable.
  obtain ⟨b, hbct, hbOpen, hbasis⟩ :=
    TopologicalSpace.exists_countable_basis (EuclideanSpace ℝ (Fin k))
  -- Step 3.1: Isolate the basis elements whose intersection with `E` is countable.
  let bad : Set (Set (EuclideanSpace ℝ (Fin k))) :=
    {U | U ∈ b ∧ Set.Countable (U ∩ E)}
  have hbad_subset : bad ⊆ b := by
    -- Step 3.1.1: Forgetting the second component shows every bad basis element lies in `b`.
    intro U hU; exact hU.1
  -- Step 3.2: The collection `bad` is countable because it sits inside the countable basis.
  have hbad_count : bad.Countable := Set.Countable.mono hbad_subset hbct
  -- Step 3.3: Any union of countably many countable sets is countable.
  have hUnionCount :
      Set.Countable (⋃ U ∈ bad, U ∩ E) := by
    refine Set.Countable.biUnion hbad_count ?_
    intro U hU; exact hU.2
  -- Step 3.4: Show that each non-condensation point of `E` lies in one of those countable pieces.
  have hBadSubset : E \ P ⊆ ⋃ U ∈ bad, U ∩ E := by
    intro x hx
    -- Step 3.4.1: Because `x ∉ P`, extract a neighbourhood with countable intersection with `E`.
    have hxWitness :
        ∃ U ∈ 𝓝 x, Set.Countable (U ∩ E) := by
      -- Step 3.4.1.1: If no such neighbourhood existed, `x` would actually lie in `P`.
      classical
      by_contra h
      have hxP' : x ∈ P := by
        refine (hcond).mpr ?_
        intro U hU
        -- Step 3.4.1.2: Producing a contradiction from a hypothetical countable intersection.
        by_contra hcnt
        exact h ⟨U, hU, hcnt⟩
      exact hx.2 hxP'
    rcases hxWitness with ⟨U, hUN, hUcnt⟩
    -- Step 3.4.2: Replace the neighbourhood with a basis element contained in it.
    obtain ⟨V, hVb, hxV, hVsub⟩ :=
      (IsTopologicalBasis.mem_nhds_iff hbasis).1 hUN
    -- Step 3.4.3: The smaller basis element still meets `E` in a countable set.
    have hVcnt : Set.Countable (V ∩ E) :=
      hUcnt.mono <| by
        intro y hy
        exact ⟨hVsub hy.1, hy.2⟩
    have hVbad : V ∈ bad := ⟨hVb, hVcnt⟩
    -- Step 3.4.4: Conclude that `x` belongs to the big countable union.
    refine Set.mem_iUnion.2 ?_
    refine ⟨V, Set.mem_iUnion.2 ?_⟩
    refine ⟨hVbad, ?_⟩
    exact ⟨hxV, hx.1⟩
  -- Step 3.5: Deduce the countability of the bad points themselves.
  have hCountBad : Set.Countable (E \ P) :=
    Set.Countable.mono hBadSubset hUnionCount
  -- Step 3.6: Note that the uncountability hypothesis already forces `E` to be nonempty.
  have hEnonempty : E.Nonempty := by
    classical
    by_contra hEmpty
    have hEmptyEq : E = (∅ : Set (EuclideanSpace ℝ (Fin k))) :=
      (Set.not_nonempty_iff_eq_empty).1 hEmpty
    have : Set.Countable E := by
      subst hEmptyEq
      exact
        (Set.countable_empty :
          Set.Countable (∅ : Set (EuclideanSpace ℝ (Fin k))))
    exact hE this
  -- Step 4: Prove that `P` is closed by showing it contains all its limit points.
  have hClosed : IsClosed P := by
    -- Step 4.1: It suffices to prove `closure P ⊆ P`.
    refine isClosed_of_closure_subset ?_
    intro x hx
    -- Step 4.2: Show that every neighbourhood of `x` meets `E` uncountably, so `x ∈ P`.
    have hxCond : ∀ U ∈ 𝓝 x, ¬ Set.Countable (U ∩ E) := by
      intro U hU
      -- Step 4.2.1: Choose an open neighbourhood inside `U`.
      rcases mem_nhds_iff.1 hU with ⟨O, hOsub, hOopen, hxO⟩
      -- Step 4.2.2: Pick a point of `P` inside that open neighbourhood.
      obtain ⟨y, ⟨hyO, hyP⟩⟩ :=
        (mem_closure_iff.1 hx) O hOopen hxO
      -- Step 4.2.3: Use the defining property of `P` at the picked point.
      have hyCond : ∀ V ∈ 𝓝 y, ¬ Set.Countable (V ∩ E) :=
        (hcond.mp hyP)
      -- Step 4.2.4: The open set `O` is a neighbourhood of `y`, so its intersection with `E` is uncountable.
      have hOuncount : ¬ Set.Countable (O ∩ E) :=
        hyCond O (hOopen.mem_nhds hyO)
      -- Step 4.2.5: A subset of a countable set would be countable, hence `U ∩ E` cannot be countable.
      exact fun hUE =>
        hOuncount <|
          Set.Countable.mono
            (by
              intro z hz
              exact ⟨hOsub hz.1, hz.2⟩)
            hUE
    -- Step 4.3: Translate the neighbourhood condition back into membership in `P`.
    exact (hcond.mpr hxCond)
  -- Step 5: Show that `P` has no isolated points, i.e., it is preperfect.
  have hPre : Preperfect P := by
    -- Step 5.1: Work with the neighbourhood characterization of accumulation points.
    rw [preperfect_iff_nhds]
    intro x hxP U hU
    -- Step 5.2: Record the uncountability of `U ∩ E`.
    have hUncount : ¬ Set.Countable (U ∩ E) :=
      (hcond.mp hxP) U hU
    -- Step 5.3: Countability of the bad part inside `U`.
    have hBadU : Set.Countable (U ∩ (E \ P)) :=
      Set.Countable.mono (Set.inter_subset_right (s := U) (t := E \ P)) hCountBad
    -- Step 5.4: Split `U ∩ E` into the good and bad pieces.
    have hsplit :
        U ∩ E = (U ∩ E ∩ P) ∪ (U ∩ (E \ P)) := by
      ext y; constructor
      · intro hy
        rcases hy with ⟨hyU, hyE⟩
        by_cases hyP : y ∈ P
        · exact Or.inl ⟨⟨hyU, hyE⟩, hyP⟩
        · exact Or.inr ⟨hyU, ⟨hyE, hyP⟩⟩
      · intro hy
        rcases hy with hy | hy
        · exact hy.1
        · exact ⟨hy.1, hy.2.1⟩
    -- Step 5.5: Conclude that the good piece `U ∩ E ∩ P` is uncountable.
    have hGood :
        ¬ Set.Countable (U ∩ E ∩ P) := by
      intro hcnt
      have : Set.Countable (U ∩ E) :=
        (hsplit.symm ▸ (Set.Countable.union hcnt hBadU))
      exact hUncount this
    -- Step 5.6: Extract a point different from `x` inside `U ∩ P`.
    have hy :
        ∃ y ∈ U ∩ E ∩ P, y ≠ x := by
      by_contra h
      have hsubset : U ∩ E ∩ P ⊆ ({x} : Set (EuclideanSpace ℝ (Fin k))) := by
        intro y hy'
        by_contra hyneq
        exact h ⟨y, hy', hyneq⟩
      exact hGood (Set.Countable.mono hsubset (Set.countable_singleton x))
    rcases hy with ⟨y, ⟨⟨hyU, _⟩, hyP⟩, hxy⟩
    -- Step 5.7: Provide the required witness in `U ∩ P`.
    exact ⟨y, ⟨hyU, hyP⟩, hxy⟩
  -- Step 6: Combine closedness and the accumulation property to conclude that `P` is perfect.
  exact ⟨hClosed, hPre⟩
