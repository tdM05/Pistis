import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Let $V$ be a vector space which is spanned by a countably infinite set. Prove that every linearly independent subset of $V$ is finite or countably infinite.
-/

/-Informal Proof

Let $A$ be the countable generating set, and let $U$ be an uncountable linearly independent set. It can be extended to a basis $B$ of the whole space. Now consider the subset $C$ of elements of $B$ that appear in the $B$-decompositions of elements of $A$.
Since only finitely many elements are involved in the decomposition of each element of $A$, the set $C$ is countable. But $C$ also clearly generates the vector space $V$. This contradicts the fact that it is a proper subset of the basis $B$ (since $B$ is uncountable).
-/

theorem Artin_exercise_3_5_6 {K V : Type*} [Field K] [AddCommGroup V]
  [Module K V] {S : Set V} (hS : Set.Countable S)
  (hS1 : span K S = ⊤) {ι : Type*} (R : ι → V)
  (hR : LinearIndependent K R) : Countable ι := by
  -- Step 1: Switch to classical logic so that we can choose witnesses for span representations.
  classical
  -- Step 2: Convert the set-level countability hypothesis into a subtype instance.
  have hS_count : Countable S := hS.to_subtype
  -- Step 2.1: Register the obtained countability instance for `S` to ease later lemmas.
  have _ : Countable S := hS_count
  -- Step 3: Control the dimension (module rank) of `V` using the countable spanning set `S`.
  have h_rank_le_S₀ : Module.rank K V ≤ Cardinal.mk S := by
    -- Step 3.1: Start from the general inequality `rank (span S) ≤ #S`.
    have h_span : Module.rank K (span K S) ≤ Cardinal.mk S :=
      rank_span_le (R := K) (M := V) (s := S)
    -- Step 3.2: Rewrite the rank of `span K S` as the rank of `V` using `span K S = ⊤`.
    have h_top_rank : Module.rank K (⊤ : Submodule K V) = Module.rank K V :=
      rank_top (R := K) (M := V)
    have h_rank_eq' : Module.rank K (⊤ : Submodule K V) = Module.rank K (span K S) := by
      simpa using congrArg (fun T : Submodule K V => Module.rank K T) hS1.symm
    have h_rank_eq : Module.rank K V = Module.rank K (span K S) :=
      by simpa [h_top_rank] using h_rank_eq'
    -- Step 3.3: Transport the inequality along the obtained equality.
    simpa [h_rank_eq] using h_span
  -- Step 3.4: Lift the inequality to align universe levels for subsequent bounds.
  have h_rank_le_S : Cardinal.lift (Module.rank K V) ≤ Cardinal.lift (Cardinal.mk S) :=
    Cardinal.lift_le.mpr h_rank_le_S₀
  -- Step 4: Bound the indexing cardinality of the linearly independent family using the rank.
  have h_card_le_rank : Cardinal.lift (Cardinal.mk ι) ≤ Cardinal.lift (Module.rank K V) :=
    hR.cardinal_lift_le_rank
  -- Step 5: Combine the two lifted inequalities to see that the index set is bounded by `#S`.
  have h_card_le_S : Cardinal.lift (Cardinal.mk ι) ≤ Cardinal.lift (Cardinal.mk S) :=
    h_card_le_rank.trans h_rank_le_S
  -- Step 6: Convert the countability of `S` into the lifted inequality `#S ≤ ℵ₀`.
  have hS_le_aleph0 : Cardinal.lift (Cardinal.mk S) ≤ Cardinal.lift Cardinal.aleph0 :=
    Cardinal.lift_le.mpr (Cardinal.mk_le_aleph0 (α := S))
  -- Step 7: Conclude that the index set is at most countable (still at the lifted level).
  have h_card_le_aleph0_lift : Cardinal.lift (Cardinal.mk ι) ≤ Cardinal.lift Cardinal.aleph0 :=
    h_card_le_S.trans hS_le_aleph0
  -- Step 7.1: Remove lifts to obtain the bound in the base universe.
  have h_card_le_aleph0 : Cardinal.mk ι ≤ Cardinal.aleph0 := by
    simpa [Cardinal.lift_id, Cardinal.lift_aleph0] using h_card_le_aleph0_lift
  -- Step 8: Translate the cardinal inequality back to the `Countable` predicate on `ι`.
  exact (Cardinal.mk_le_aleph0_iff).mp h_card_le_aleph0

/-
Correction summary:

The original statement assumed only `Set.Countable S`, so it formalized a
space spanned by an at-most-countable set, not necessarily by a countably
infinite set as in the informal theorem.

The corrected statement adds `_hSinf : S.Infinite`, so `hS` and `_hSinf`
together express that `S` is countably infinite.  The spanning hypothesis
`span K S = ⊤` and the conclusion `Countable ι` for a linearly independent
family `R : ι → V` then exactly say that every linearly independent subset is
finite or countably infinite.

The new infinitude hypothesis is not needed in the proof, since the proved
cardinality bound is actually slightly stronger, but it makes the Lean
statement faithful to the informal claim.
-/
theorem Artin_exercise_3_5_6_corrected {K V : Type*} [Field K] [AddCommGroup V]
  [Module K V] {S : Set V} (hS : Set.Countable S) (_hSinf : S.Infinite)
  (hS1 : span K S = ⊤) {ι : Type*} (R : ι → V)
  (hR : LinearIndependent K R) : Countable ι := by
  classical
  -- Step 2: Convert the set-level countability hypothesis into a subtype instance.
  have hS_count : Countable S := hS.to_subtype
  -- Step 2.1: Register the obtained countability instance for `S` to ease later lemmas.
  have _ : Countable S := hS_count
  -- Step 3: Control the dimension (module rank) of `V` using the countable spanning set `S`.
  have h_rank_le_S₀ : Module.rank K V ≤ Cardinal.mk S := by
    -- Step 3.1: Start from the general inequality `rank (span S) ≤ #S`.
    have h_span : Module.rank K (span K S) ≤ Cardinal.mk S :=
      rank_span_le (R := K) (M := V) (s := S)
    -- Step 3.2: Rewrite the rank of `span K S` as the rank of `V` using `span K S = ⊤`.
    have h_top_rank : Module.rank K (⊤ : Submodule K V) = Module.rank K V :=
      rank_top (R := K) (M := V)
    have h_rank_eq' : Module.rank K (⊤ : Submodule K V) = Module.rank K (span K S) := by
      simpa using congrArg (fun T : Submodule K V => Module.rank K T) hS1.symm
    have h_rank_eq : Module.rank K V = Module.rank K (span K S) :=
      by simpa [h_top_rank] using h_rank_eq'
    -- Step 3.3: Transport the inequality along the obtained equality.
    simpa [h_rank_eq] using h_span
  -- Step 3.4: Lift the inequality to align universe levels for subsequent bounds.
  have h_rank_le_S : Cardinal.lift (Module.rank K V) ≤ Cardinal.lift (Cardinal.mk S) :=
    Cardinal.lift_le.mpr h_rank_le_S₀
  -- Step 4: Bound the indexing cardinality of the linearly independent family using the rank.
  have h_card_le_rank : Cardinal.lift (Cardinal.mk ι) ≤ Cardinal.lift (Module.rank K V) :=
    hR.cardinal_lift_le_rank
  -- Step 5: Combine the two lifted inequalities to see that the index set is bounded by `#S`.
  have h_card_le_S : Cardinal.lift (Cardinal.mk ι) ≤ Cardinal.lift (Cardinal.mk S) :=
    h_card_le_rank.trans h_rank_le_S
  -- Step 6: Convert the countability of `S` into the lifted inequality `#S ≤ ℵ₀`.
  have hS_le_aleph0 : Cardinal.lift (Cardinal.mk S) ≤ Cardinal.lift Cardinal.aleph0 :=
    Cardinal.lift_le.mpr (Cardinal.mk_le_aleph0 (α := S))
  -- Step 7: Conclude that the index set is at most countable (still at the lifted level).
  have h_card_le_aleph0_lift : Cardinal.lift (Cardinal.mk ι) ≤ Cardinal.lift Cardinal.aleph0 :=
    h_card_le_S.trans hS_le_aleph0
  -- Step 7.1: Remove lifts to obtain the bound in the base universe.
  have h_card_le_aleph0 : Cardinal.mk ι ≤ Cardinal.aleph0 := by
    simpa [Cardinal.lift_id, Cardinal.lift_aleph0] using h_card_le_aleph0_lift
  -- Step 8: Translate the cardinal inequality back to the `Countable` predicate on `ι`.
  exact (Cardinal.mk_le_aleph0_iff).mp h_card_le_aleph0
