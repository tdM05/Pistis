import Mathlib

open Filter Real Function Set
open scoped Topology



/-Informal Statement

Give a direct proof that the nested decreasing intersection of nonempty covering compact sets is nonempty.
-/

/-Informal Proof

Let
$$
A_1 \supset A_2 \supset \cdots \supset A_n \supset \cdots
$$
be a nested decreasing sequence of compacts. Suppose that $\bigcap A_n=\emptyset$. Take $U_n=A_n^c$, then
$$
\bigcup U_n=\bigcup A_n^c=\left(\bigcap A_n\right)^c=A_1 .
$$
Here, I'm thinking of $A_1$ as the main metric space. Since $\left\{U_n\right\}$ is an open covering of $A_1$, we can extract a finite subcovering, that is,
$$
A_{\alpha_1}^c \cup A_{\alpha_2}^c \cup \cdots \cup A_{\alpha_m}^c \supset A_1
$$
or
$$
\left(A_1 \backslash A_{\alpha_1}\right) \cup\left(A_1 \backslash A_{\alpha_2}\right) \cup \cdots \cup\left(A_1 \backslash A_{\alpha_m}\right) \supset A_1 .
$$
But, this is true only if $A_{\alpha_i}=\emptyset$ for some $i$, a contradiction.
-/

theorem Pugh_exercise_2_92 {α : Type*} [TopologicalSpace α]
  {s : ℕ → Set α}
  (hs : ∀ i, IsCompact (s i))
  (hne : ∀ i, (s i).Nonempty)
  (hs : ∀ i, (s i) ⊇ (s (i + 1))) :
  (⋂ i, s i).Nonempty := by
  sorry

/-
The informal proof forgets that compact subsets need not be closed when the ambient space is not
Hausdorff. In a non-Hausdorff compact space (for instance the cofinite topology on `ℕ`), one can
produce nested, nonempty, compact sets whose intersection is empty. The failure happens precisely
because compactness alone does not force the finite intersection property for nested families
unless the sets are also closed in a compact space.
-/

namespace Exercise292

open scoped Topology

/-- The counterexample uses the cofinite topology on `ℕ`; the `n`-th set is the tail `{x | n ≤ x}`. -/
def cofiniteChain (n : ℕ) : Set (CofiniteTopology ℕ) :=
  {x | n ≤ ((CofiniteTopology.of (X := ℕ)).symm x)}

lemma cofiniteChain_isCompact (n : ℕ) :
    IsCompact (cofiniteChain n : Set (CofiniteTopology ℕ)) := by
  -- Step 1: use that `CofiniteTopology ℕ` is Noetherian, hence every subset is compact.
  simpa [cofiniteChain] using
    (TopologicalSpace.NoetherianSpace.isCompact
      (α := CofiniteTopology ℕ) (s := cofiniteChain n))

lemma cofiniteChain_nonempty (n : ℕ) :
    (cofiniteChain n : Set (CofiniteTopology ℕ)).Nonempty := by
  -- Step 1: exhibit the point `n` itself, which clearly satisfies `n ≤ n`.
  refine ⟨(CofiniteTopology.of (X := ℕ)) n, ?_⟩
  simp [cofiniteChain]

lemma cofiniteChain_succ_subset (n : ℕ) :
    cofiniteChain n ⊇ cofiniteChain (n + 1) := by
  -- Step 1: unfold the two sets and chase inequalities.
  -- Step 2: given `x` with `n + 1 ≤ x`, deduce `n ≤ x` via transitivity.
  change cofiniteChain (n + 1) ⊆ cofiniteChain n
  intro x hx
  dsimp [cofiniteChain] at hx ⊢
  exact le_trans (Nat.le_succ _) hx

lemma cofiniteChain_intersection_empty :
    ¬ (⋂ i, cofiniteChain i : Set (CofiniteTopology ℕ)).Nonempty := by
  -- Step 1: suppose towards contradiction that some `x` lies in every tail.
  intro h
  rcases h with ⟨x, hx_mem⟩
  have hx := Set.mem_iInter.mp hx_mem
  -- Step 2: instantiate `hx` with `k + 1` (where `k` is the underlying natural number of `x`)
  -- to obtain the impossible inequality `k + 1 ≤ k`.
  set k : ℕ := (CofiniteTopology.of (X := ℕ)).symm x with hk
  have hx' : k + 1 ≤ k := by
    simpa [cofiniteChain, k, hk] using hx (k + 1)
  -- Step 3: combine `x < x + 1` with `x + 1 ≤ x` to obtain `x < x`, contradiction.
  have : k < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hx'
  exact lt_irrefl _ this

def exercise_2_92_statement : Prop :=
  ∀ {α : Type} [TopologicalSpace α] {s : ℕ → Set α},
    (∀ i, IsCompact (s i)) →
    (∀ i, (s i).Nonempty) →
    (∀ i, s i ⊇ s (i + 1)) →
    (⋂ i, s i).Nonempty

theorem Pugh_exercise_2_92_neg :
    ¬ exercise_2_92_statement := by
  classical
  -- Step 1: assume the original statement holds and instantiate it in the cofinite topology.
  intro h
  -- Step 2: define the specific decreasing chain.
  let s : ℕ → Set (CofiniteTopology ℕ) := fun n => cofiniteChain n
  -- Step 3: collect the three hypotheses required by the statement.
  have hcomp : ∀ n, IsCompact (s n) := cofiniteChain_isCompact
  have hne : ∀ n, (s n).Nonempty := cofiniteChain_nonempty
  have hmono : ∀ n, s n ⊇ s (n + 1) := cofiniteChain_succ_subset
  -- Step 4: apply the assumed theorem to `s` and contradict the explicit emptiness computation.
  have : (⋂ i, s i).Nonempty :=
    h (α := CofiniteTopology ℕ) (s := s) hcomp hne hmono
  -- Step 5: use `cofiniteChain_intersection_empty` to contradict the derived non-emptiness.
  exact cofiniteChain_intersection_empty this

/-
Corrected statement: in a Hausdorff space (e.g. a metric space), compact subsets are closed, so a
nested sequence of nonempty compact sets has the finite intersection property inside the compact
set `s 0`, forcing the overall intersection to be nonempty.
-/

theorem Pugh_exercise_2_92_corrected {α : Type*} [TopologicalSpace α] [T2Space α]
    {s : ℕ → Set α}
    (hcomp : ∀ i, IsCompact (s i))
    (hne : ∀ i, (s i).Nonempty)
    (hmono : ∀ i, s i ⊇ s (i + 1)) :
    (⋂ i, s i).Nonempty := by
  -- Step 1: package the monotonicity assumption in the `⊆` direction.
  have hmono' : ∀ i, s (i + 1) ⊆ s i := fun i => hmono i
  -- Step 2: note that compact subsets are closed in a Hausdorff space.
  have hclosed : ∀ i, IsClosed (s i) := fun i => (hcomp i).isClosed
  -- Step 3: appeal to the Cantor intersection theorem for decreasing sequences of compact sets.
  exact
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed s hmono' hne
      (hcomp 0) hclosed

end Exercise292
