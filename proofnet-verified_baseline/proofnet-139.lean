import Mathlib

open Filter Real Function
open scoped Topology



/-Informal Statement

Suppose that $E$ is an uncountable subset of $\mathbb{R}$. Prove that there exists a point $p \in \mathbb{R}$ at which $E$ condenses.
-/

/-Informal Proof

I think this is the proof by contrapositive that you were getting at.
Suppose that $E$ has no limit points at all. Pick an arbitrary point $x \in E$. Then $x$ cannot be a limit point, so there must be some $\delta>0$ such that the ball of radius $\delta$ around $x$ contains no other points of $E$ :
$$
B_\delta(x) \cap E=\{x\}
$$
Call this "point 1 ". For the next point, take the closest element to $x$ and on its left; that is, choose the point
$$
\max [E \cap(-\infty, x)]
$$
if it exists (that is important - if not, skip to the next step). Note that by the argument above, this supremum, should it exist, cannot equal $x$ and is therefore a new point in $E$.

Call this "point 2 ". Now take the first point to the right of $x$ for "point 3 ". Take the first point to the left of point 2 for "point 4 ". And so on, ad infinitum.

This gives a countable list of unique points; we must show that it exhausts the entire set $E$. Suppose not. Suppose there is some element $a<x$ which is never included in the list (picking $a$ on the negative side of $x$ is arbitrary, and the same argument would work for the second case). Then the element closest and to the right of $a$ in $E$ (which exists, by the no-limit-points argument at the beginning) is also not in the list; if it was, $a$ would have been in one of the next two spots. And same with that point (call it $a_1$ ); there is a closest $a_2>a_1 \in E$ such that $a_2$ is not in the list. Repeating, we generate an infinite monotone-increasing sequence $\left\{a_i\right\}$ of elements in $E$ and not in the list, which is clearly bounded above by $x$. By the Monotone
Convergence Theorem this sequence has a limit. But that means the sequence $\left\{a_i\right\} \subset E$ converges to a limit, and hence $E$ has a limit point, contradicting the assumption. Therefore our list exhausts $E$, and we have enumerated all its elements.
-/

theorem Pugh_exercise_2_126 {E : Set ℝ}
  (hE : ¬ Set.Countable E) : ∃ (p : ℝ), ClusterPt p (𝓟 E) := by
  -- Step 1: Show that the uncountable set `E` must be nonempty, otherwise it would be countable.
  classical
  have hEnonempty : E.Nonempty := by
    -- Step 1.1: Assume for contradiction that `E` has no elements.
    by_contra hEmpty
    -- Step 1.2: Convert the assumption into the concrete statement `E = ∅`.
    have hEq : E = (∅ : Set ℝ) := by
      ext x
      constructor
      · intro hx
        -- Step 1.2.1: `x ∈ E` contradicts the assumption that no element of `E` exists.
        have hxNot : x ∉ E := (not_exists.mp hEmpty) x
        exact (hxNot hx).elim
      · intro hx
        -- Step 1.2.2: Membership in the empty set is already impossible.
        exact hx.elim
    -- Step 1.3: Rewrite the countability statement via `hEq` and contradict `hE`.
    have hCount : Set.Countable E := by
      -- Step 1.3.1: Simplify the goal using `hEq` so that it becomes the known fact that `∅` is countable.
      simp [hEq]
    exact hE hCount
  -- Step 2: Extract a specific element `p` from `E` to serve as the eventual cluster point.
  obtain ⟨p, hp⟩ := hEnonempty
  -- Step 3: Prove that this element `p` is a cluster point of the principal filter on `E`.
  refine ⟨p, ?_⟩
  -- Step 3.1: Use the characterization of cluster points for principal filters.
  refine clusterPt_principal_iff.mpr ?_
  -- Step 3.2: Every neighborhood of `p` already contains `p`, so it meets `E`.
  intro U hU
  -- Step 3.2.1: Record that `p` lies in each neighborhood `U`.
  have hpU : p ∈ U := mem_of_mem_nhds hU
  -- Step 3.2.2: Exhibit `p` as a witness in the intersection `U ∩ E`.
  exact ⟨p, ⟨hpU, hp⟩⟩

/-
Problems with the original formalization:

The informal statement asks for a *condensation point* of `E` — a point `p`
such that every neighborhood of `p` contains **uncountably many** points of
`E`. The original Lean translation uses `ClusterPt p (𝓟 E)`, which only says
that every neighborhood of `p` meets `E` (every neighborhood contains at least
one point of `E`). That is strictly weaker: any element of `E` is a cluster
point of the principal filter on `E`, regardless of cardinality.

The corrected statement spells out condensation directly:
  `∀ U ∈ 𝓝 p, ¬ Set.Countable (U ∩ E)`.
The proof is the standard Lindelöf argument: if no such `p` existed, every
real would have an open neighborhood meeting `E` only countably, and second
countability of `ℝ` would extract a countable subcover, forcing `E` itself
to be a countable union of countable sets — contradicting uncountability.
-/

/-- Corrected statement: there is a genuine *condensation point* of `E`,
i.e. a point `p` such that every neighborhood of `p` meets `E` in an
uncountable set. -/
theorem Pugh_exercise_2_126_corrected {E : Set ℝ}
    (hE : ¬ Set.Countable E) :
    ∃ p : ℝ, ∀ U ∈ 𝓝 p, ¬ Set.Countable (U ∩ E) := by
  classical
  -- Step 1: Argue by contradiction.
  by_contra hno
  push_neg at hno
  -- Step 2: For each `p`, refine the witnessing neighborhood into an open one.
  have hOpen :
      ∀ p : ℝ, ∃ V : Set ℝ, IsOpen V ∧ p ∈ V ∧ Set.Countable (V ∩ E) := by
    intro p
    obtain ⟨U, hUmem, hUcount⟩ := hno p
    obtain ⟨V, hVU, hVopen, hpV⟩ := mem_nhds_iff.mp hUmem
    exact ⟨V, hVopen, hpV, hUcount.mono (Set.inter_subset_inter_left _ hVU)⟩
  choose V hVopen hpV hVcount using hOpen
  -- Step 3: The opens `V p` cover `ℝ` because `p ∈ V p`.
  have hcover : ⋃ p : ℝ, V p = (Set.univ : Set ℝ) :=
    Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨x, hpV x⟩
  -- Step 4: Second-countability of `ℝ` extracts a countable subcover.
  obtain ⟨T, hTcount, hTu⟩ := TopologicalSpace.isOpen_iUnion_countable V hVopen
  -- Step 5: Hence `E` is contained in a countable union of countable sets.
  have hEsub : E ⊆ ⋃ p ∈ T, V p ∩ E := by
    intro x hxE
    have hxUniv : x ∈ ⋃ p, V p := hcover ▸ Set.mem_univ x
    rw [← hTu] at hxUniv
    obtain ⟨p, hpT, hxV⟩ := Set.mem_iUnion₂.mp hxUniv
    exact Set.mem_iUnion₂.mpr ⟨p, hpT, hxV, hxE⟩
  -- Step 6: Conclude `E` countable, contradicting the hypothesis.
  exact hE <| (hTcount.biUnion fun p _ => hVcount p).mono hEsub
