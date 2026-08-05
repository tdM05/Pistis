import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Let $A$ be a nonempty set of real numbers which is bounded below. Let $-A$ be the set of all numbers $-x$, where $x \in A$. Prove that $\inf A=-\sup (-A)$.
-/

/-Informal Proof

We need to prove that $-\sup (-A)$ is the greatest lower bound of $A$. For brevity, let $\alpha=-\sup (-A)$. We need to show that $\alpha \leq x$ for all $x \in A$ and $\alpha \geq \beta$ if $\beta$ is any lower bound of $A$.

Suppose $x \in A$. Then, $-x \in-A$, and, hence $-x \leq \sup (-A)$. It follows that $x \geq-\sup (-A)$, i.e., $\alpha \leq x$. Thus $\alpha$ is a lower bound of $A$.

Now let $\beta$ be any lower bound of $A$. This means $\beta \leq x$ for all $x$ in $A$. Hence $-x \leq-\beta$ for all $x \in A$, which says $y \leq-\beta$ for all $y \in-A$. This means $-\beta$ is an upper bound of $-A$. Hence $-\beta \geq \sup (-A)$ by definition of sup, i.e., $\beta \leq-\sup (-A)$, and so $-\sup (-A)$ is the greatest lower bound of $A$.
-/

theorem Rudin_exercise_1_5 (A minus_A : Set ℝ) (hA : A.Nonempty)
  (hA_bdd_below : BddBelow A) (hminus_A : minus_A = {x | -x ∈ A}) :
  Min A = Max minus_A := by
  sorry


/-
The original formalization is not faithful to the informal statement.

The informal statement is about the infimum and supremum of sets of real numbers:
`inf A = -sup (-A)`. In Mathlib these are written as `sInf A` and `sSup minus_A`.
The expression `Min A = Max minus_A` does not say this.

For `A : Set ℝ`, Lean reads `Min A` and `Max minus_A` through typeclass notation on the corresponding subtype, not as the real numbers `inf A` and `sup minus_A`. Thus the original statement is comparing the wrong objects.

The corrected version below fixes the conclusion to the actual real-valued claim:
`sInf A = -sSup minus_A`. The hypothesis
`hminus_A : minus_A = {x | -x ∈ A}` correctly describes the negated set, so no change is
needed there.
-/
theorem Rudin_exercise_1_5_corrected (A minus_A : Set ℝ) (hA : A.Nonempty)
  (hA_bdd_below : BddBelow A) (hminus_A : minus_A = {x | -x ∈ A}) :
  sInf A = - sSup minus_A := by
  -- Step 1: Switch to classical logic so that we can choose explicit witnesses from the hypotheses.
  classical
  -- Step 2: Store reusable copies of the nonemptiness and bounded-below hypotheses.
  have hA_nonempty : A.Nonempty := hA
  have hA_bdd_below_copy : BddBelow A := hA_bdd_below
  -- Step 3: Extract an element `a ∈ A` to witness that `minus_A` is nonempty.
  obtain ⟨a, ha⟩ := hA
  -- Step 3.1: Use `a` to produce an element of `minus_A`, proving its nonemptiness.
  have hminus_nonempty : minus_A.Nonempty := by
    refine ⟨-a, ?_⟩
    simpa [hminus_A] using ha
  -- Step 4: Transfer the lower bound on `A` to an upper bound on `minus_A` via negation.
  obtain ⟨m, hm⟩ := hA_bdd_below
  -- Step 4.1: Negating the lower-bound witness gives an upper-bound witness for `minus_A`.
  have hminus_bddAbove : BddAbove minus_A := by
    refine ⟨-m, ?_⟩
    intro y hy
    -- Step 4.1.1: Translate membership in `minus_A` to membership of the negation in `A`.
    have hyA : -y ∈ A := by
      simpa [hminus_A] using hy
    -- Step 4.1.2: Apply the lower-bound inequality and negate it to bound `y` from above.
    have hm_le : m ≤ -y := hm hyA
    simpa [neg_neg] using (neg_le_neg hm_le)
  -- Step 5: Show that `-sSup minus_A` is a lower bound for every element of `A`.
  have hLowerBound : ∀ x ∈ A, -sSup minus_A ≤ x := by
    intro x hx
    -- Step 5.1: Convert `x ∈ A` into a statement about `-x ∈ minus_A`.
    have hx_minus : -x ∈ minus_A := by
      simpa [hminus_A] using hx
    -- Step 5.2: Use the definition of `sSup` as a least upper bound, then negate.
    have hx_le : -x ≤ sSup minus_A := le_csSup hminus_bddAbove hx_minus
    simpa [neg_neg] using (neg_le_neg hx_le)
  -- Step 6: Invoke the greatest-lower-bound property of `sInf` with the previous step.
  have h_le_right : -sSup minus_A ≤ sInf A := le_csInf hA_nonempty hLowerBound
  -- Step 7: Prove that every element of `minus_A` is bounded above by `-sInf A`.
  have hUpperBound : ∀ y ∈ minus_A, y ≤ -sInf A := by
    intro y hy
    -- Step 7.1: Relate `y ∈ minus_A` back to `-y ∈ A`.
    have hyA : -y ∈ A := by
      simpa [hminus_A] using hy
    -- Step 7.2: Apply the defining inequality for `sInf` and negate the result.
    have hInf_le : sInf A ≤ -y := csInf_le hA_bdd_below_copy hyA
    simpa [neg_neg] using (neg_le_neg hInf_le)
  -- Step 8: Apply the least-upper-bound characterization of `sSup` to the previous bound.
  have h_sup_le : sSup minus_A ≤ -sInf A := csSup_le hminus_nonempty hUpperBound
  -- Step 9: Negate the inequality from Step 8 to obtain `sInf A ≤ -sSup minus_A`.
  have h_le_left : sInf A ≤ -sSup minus_A := by
    simpa [neg_neg] using (neg_le_neg h_sup_le)
  -- Step 10: Combine the two opposite inequalities to reach the desired equality.
  exact le_antisymm h_le_left h_le_right

/-
Metatheoretic relative-independence sketch for the original target.

The original conclusion
`Min A = Max minus_A` is not a real-valued statement. It elaborates as the type equality
`Min ↑A = Max ↑minus_A`, where `Min` and `Max` are the one-field typeclass structures
containing binary operations named `min` and `max`.

The hypotheses decide the relevant extensional content: negation gives an equivalence between
the subtype `A` and the subtype `minus_A`, and this transports binary operations on `A` to
binary operations on `minus_A`. Thus the ordinary mathematical consequence is
`Min A ≃ Max minus_A`, which is proved below.

The gap is exactly the intensional gap between equivalence and equality of types. This gives the
following relative independence picture.

* Positive side: in an extension of Lean with a type-extensionality or univalence-style
  principle `(α ≃ β) → α = β`, the original target follows from the equivalence below. This
  direction is formalized by `Rudin_exercise_1_5_original_from_type_extensionality`.

* Negative side: in the usual intensional/syntactic reading of Lean's type theory, type equality
  is generated by reflexivity/definitional equality and explicit equality eliminators. The two
  sides have different head structure constants, `Min` and `Max`, so the equivalence below does
  not itself generate a term of `Min A = Max minus_A`. Showing this as a genuine non-provability
  theorem would require formalizing Lean's metatheory, such as a term model/canonicity argument,
  not just proving an ordinary theorem about real sets in Mathlib.

This is not the same kind of phenomenon as `Con(PA)` or CH. `Con(PA)` is a meaningful arithmetical
sentence that is true in the standard natural numbers, assuming PA is consistent, but not provable
in PA. CH is a meaningful set-theoretic sentence whose truth can vary between models of set
theory. By contrast, the present statement is a formalization artifact: it accidentally asks for
equality of Lean type expressions where the intended mathematical content only supplies an
equivalence of types.

Thus this file does not contain a kernel-checked absolute independence theorem. It records the
metatheoretic reason for the independence claim and formalizes the positive relative direction.
It also records the strongest statement available from the given hypotheses in standard Lean,
namely equivalence rather than equality.
-/

-- The next declarations are `def`s, not `theorem`s, because an equivalence such as `A ≃ minus_A`
-- is data living in `Type`, not a proposition living in `Prop`. Lean theorem declarations must
-- prove propositions; explicit equivalence data is defined with `def`.

-- Negation gives the equivalence between the subtype of elements of `A` and the
-- subtype of elements of `minus_A`.
private def Rudin_exercise_1_5_negSubtypeEquiv (A minus_A : Set ℝ)
    (hminus_A : minus_A = {x | -x ∈ A}) : A ≃ minus_A where
  -- Send an element `x : A` to `-x`, viewed as an element of `minus_A`.
  toFun x := ⟨-x.1, by simp [hminus_A, x.2]⟩
  -- The inverse map is also negation: if `y ∈ minus_A`, then `-y ∈ A`.
  invFun y := ⟨-y.1, by simpa [hminus_A] using y.2⟩
  -- Negating twice brings every element of `A` back to itself.
  left_inv := by
    intro x
    ext
    simp
  -- The same double-negation argument proves the right inverse law on `minus_A`.
  right_inv := by
    intro y
    ext
    simp

-- An equivalence `α ≃ β` transports binary operations on `α` to binary
-- operations on `β`. Since `Min α` and `Max β` are just wrappers around binary
-- operations, this gives an equivalence `Min α ≃ Max β`.
private def Rudin_exercise_1_5_minEquivMaxOfEquiv {α β : Type} (e : α ≃ β) :
    Min α ≃ Max β where
  -- Convert a `min` operation on `α` into a `max` operation on `β` by moving
  -- inputs back to `α`, applying the old operation, and moving the result to `β`.
  toFun m := ⟨fun x y => e (m.min (e.symm x) (e.symm y))⟩
  -- Convert in the other direction by the same transport using `e.symm`.
  invFun m := ⟨fun x y => e.symm (m.max (e x) (e y))⟩
  -- Transporting forward and then backward is the identity on `Min α`.
  left_inv := by
    intro m
    cases m with
    | mk f =>
      simp [Equiv.symm_apply_apply]
  -- Transporting backward and then forward is the identity on `Max β`.
  right_inv := by
    intro m
    cases m with
    | mk f =>
      simp [Equiv.apply_symm_apply]

-- This is the strongest standard Lean conclusion from the original hypotheses:
-- the two sides of the bad equality are equivalent as types.
def Rudin_exercise_1_5_original_equiv (A minus_A : Set ℝ) (_hA : A.Nonempty)
    (_hA_bdd_below : BddBelow A) (hminus_A : minus_A = {x | -x ∈ A}) :
    Min A ≃ Max minus_A := by
  -- First identify the subtypes `A` and `minus_A` by negation, then transport
  -- binary operations across that subtype equivalence.
  exact Rudin_exercise_1_5_minEquivMaxOfEquiv
    (Rudin_exercise_1_5_negSubtypeEquiv A minus_A hminus_A)

-- If one assumes the extra principle that equivalent types are equal, then the
-- original bad target follows immediately from the equivalence above.
theorem Rudin_exercise_1_5_original_from_type_extensionality
    (typeExt : ∀ {α β : Type}, (α ≃ β) → α = β)
    (A minus_A : Set ℝ) (hA : A.Nonempty) (hA_bdd_below : BddBelow A)
    (hminus_A : minus_A = {x | -x ∈ A}) :
    Min A = Max minus_A := by
  -- Apply the assumed type-extensionality principle to the previously built equivalence.
  exact typeExt (Rudin_exercise_1_5_original_equiv A minus_A hA hA_bdd_below hminus_A)
