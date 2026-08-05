import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Suppose $E\subset\mathbb{R}^k$ is uncountable, and let $P$ be the set of condensation points of $E$. Prove that at most countably many points of $E$ are not in $P$.
-/

/-Informal Proof

If $x \in W^c$, and $O$ is any neighborhood of $x$, then $x \in V_n \subseteq O$ for some n. Since $x \notin W, V_n \cap E$ is uncountable. Hence $O$ contains uncountably many points of $E$, and so $x$ is a condensation point of $E$. Thus $x \in P$, i.e., $W^c \subseteq P$.
Conversely if $x \in W$, then $x \in V_n$ for some $V_n$ such that $V_n \cap E$ is countable. Hence $x$ has a neighborhood (any neighborhood contained in $V_n$ ) containing at most a countable set of points of $E$, and so $x \notin P$, i.e., $W \subseteq P^c$. Hence $P=W^c$.
It is clear that $P$ is closed (since its complement $W$ is open), so that we need only show that $P \subseteq P^{\prime}$. Hence suppose $x \in P$, and $O$ is any neighborhood of $x$. (By definition of $P$ this means $O \cap E$ is uncountable.) We need to show that there is a point $y \in P \cap(O \backslash\{x\})$. If this is not the case, i.e., if every point $y$ in $O \backslash\{x\}$ is in $P^c$, then for each such point $y$ there is a set $V_n$ containing $y$ such that $V_n \cap E$ is at most countable. That would mean that $y \in W$, i.e., that $O \backslash\{x\}$ is contained in $W$. It would follow that $O \cap E \subseteq\{x\} \cup(W \cap E)$, and so $O \cap E$ contains at most a countable set of points, contrary to the hypothesis that $x \in P$. Hence $O$ contains a point of $P$ different from $x$, and so $P \subseteq P^{\prime}$. Thus $P$ is perfect.
-/

theorem Rudin_exercise_2_27b (k : ℕ) (E P : Set (EuclideanSpace ℝ (Fin k)))
  (hE : ¬ Set.Countable E)
  (hP : P = {x | ∀ U ∈ 𝓝 x, ¬ Set.Countable (U ∩ E)}) :
  Set.Countable (E \ P) := by
  classical
  -- Step 0: The uncountability of `E` implies it is nonempty, preventing trivial counterexamples.
  have hEnonempty : E.Nonempty := by
    by_contra hEmpty
    have hEmptySet :
        E = (∅ : Set (EuclideanSpace ℝ (Fin k))) :=
      (Set.not_nonempty_iff_eq_empty).1 hEmpty
    have hcount : Set.Countable E :=
      hEmptySet ▸
        (Set.countable_empty :
          Set.Countable (∅ : Set (EuclideanSpace ℝ (Fin k))))
    exact hE hcount
  -- Step 1: Choose a concrete countable basis for the Euclidean space containing `E`.
  obtain ⟨B, hBcount, -, hBbasis⟩ :=
    TopologicalSpace.exists_countable_basis
      (α := EuclideanSpace ℝ (Fin k))
  -- Step 2: Define a candidate countable union that will capture all non-condensation points.
  set G :=
      ⋃ V ∈ B,
        (if h : Set.Countable (V ∩ E) then V ∩ E else (∅ : Set (EuclideanSpace ℝ (Fin k))))
    with hGdef
  -- Step 3: Prove that each point of `E \ P` actually belongs to the union `G`.
  have hsubset : E \ P ⊆ G := by
    -- Step 3.1: Fix an arbitrary element `x` of `E \ P`.
    intro x hx
    -- Step 3.1.1: Record the facts `x ∈ E` and `x ∉ P`.
    have hxE : x ∈ E := hx.1
    have hxnotP : x ∉ P := hx.2
    -- Step 3.2: Because `x ∉ P`, find a neighborhood with countable intersection with `E`.
    have hxnotCond : ¬ ∀ U ∈ 𝓝 x, ¬ Set.Countable (U ∩ E) := by
      simpa [Set.mem_setOf_eq, hP] using hxnotP
    obtain ⟨U, hU⟩ := not_forall.mp hxnotCond
    have hUdata : U ∈ 𝓝 x ∧ ¬¬ Set.Countable (U ∩ E) := Classical.not_imp.mp hU
    have hU_mem : U ∈ 𝓝 x := hUdata.1
    have hUcountable : Set.Countable (U ∩ E) := not_not.mp hUdata.2
    -- Step 3.3: Refine that neighborhood to a basis element still having countable intersection.
    obtain ⟨V, hVB, hxV, hVsubset⟩ :=
      (hBbasis.mem_nhds_iff).1 hU_mem
    have hVsubsetUE : V ∩ E ⊆ U ∩ E := by
      -- Step 3.3.1: Any point of `V ∩ E` automatically belongs to `U ∩ E`.
      intro y hy
      exact ⟨hVsubset hy.1, hy.2⟩
    have hVcount : Set.Countable (V ∩ E) :=
      hUcountable.mono hVsubsetUE
    -- Step 3.4: Show that `x` lies in the union described by `G`.
    have hxVE : x ∈ V ∩ E := ⟨hxV, hxE⟩
    have hxInUnion :
        x ∈ ⋃ V ∈ B,
            (if h : Set.Countable (V ∩ E) then V ∩ E else (∅ : Set (EuclideanSpace ℝ (Fin k)))) := by
      -- Step 3.4.1: Exhibit the specific basis element `V` witnessing the membership.
      refine Set.mem_iUnion.2 ?_
      refine ⟨V, Set.mem_iUnion.2 ?_⟩
      refine ⟨hVB, ?_⟩
      -- Step 3.4.2: Inside that branch, use the countability of `V ∩ E` to place `x`.
      simp [hVcount, hxVE]
    -- Step 3.4.3: Rewrite the previous statement back in terms of `G`.
    have hxInG : x ∈ G := by
      change x ∈
          ⋃ V ∈ B,
            (if h : Set.Countable (V ∩ E) then V ∩ E else
              (∅ : Set (EuclideanSpace ℝ (Fin k))))
      exact hxInUnion
    exact hxInG
  -- Step 4: Establish that the union `G` itself is countable.
  have hGcount :
      Set.Countable
        (⋃ V ∈ B,
            (if h : Set.Countable (V ∩ E) then V ∩ E else (∅ : Set (EuclideanSpace ℝ (Fin k))))) := by
    -- Step 4.1: Apply `Countable.biUnion` using the countability of the basis.
    refine hBcount.biUnion ?_
    intro V hVB
    -- Step 4.2: Each summand is countable because both branches of the `if` are.
    split_ifs with hcount
    · exact hcount
    · exact (Set.countable_empty :
        Set.Countable (∅ : Set (EuclideanSpace ℝ (Fin k))))
  have hG : Set.Countable G := by
    -- Step 4.3: Translate the previous statement to the named set `G`.
    simpa [hGdef] using hGcount
  -- Step 5: Conclude that `E \ P` is countable as a subset of the countable set `G`.
  exact hG.mono hsubset
