import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Prove that $x^2+x+1$ is irreducible in the field $\mathbb{F}_2$.
-/

/-Informal Proof

If $x^2+x+1$ were reducible in $\mathbb{F}_2$, its factors must be linear. But we neither have that $0^2+0+1=$ nor $1^2+1+1=0$, therefore $x^2+x+1$ is irreducible.
-/

theorem Artin_exercise_11_4_6a {F : Type*} [Field F] [Fintype F] (hF : card F = 2) :
  Irreducible (X ^ 2 + X + 1 : Polynomial F) := by
  classical
  -- Step 1: Prove that every element of `F` must be either `0` or `1`, since the field has only two elements.
  have hx01 : ∀ x : F, x = 0 ∨ x = 1 := by
    -- Step 1.1: Assume an element `x` avoids the set `{0, 1}` and derive a contradiction with the cardinality condition.
    intro x
    by_contra hx
    -- Step 1.2: Separate the negated disjunction into the explicit inequalities `x ≠ 0` and `x ≠ 1`.
    push_neg at hx
    obtain ⟨hx0, hx1⟩ := hx
    -- Step 1.3: Build the finite set `{0, 1}` and check that adding `x` would force at least three distinct elements.
    set S : Finset F := ({0, 1} : Finset F)
    have hxS : x ∉ S := by
      -- Step 1.3.1: Membership in `{0, 1}` contradicts one of the inequalities, so `x` is not in `S`.
      simp [S, hx0, hx1]
    have hScard : S.card = 2 := by
      -- Step 1.3.2: The set `{0, 1}` obviously has two elements because `0 ≠ 1` in any field.
      simp [S, zero_ne_one]
    have hcardInsert : (insert x S).card = 3 := by
      -- Step 1.3.3: Inserting a genuinely new element raises the cardinality by one.
      simp [Finset.card_insert_of_notMem, hxS, hScard]
    have hcontr : (3 : ℕ) ≤ Fintype.card F := by
      -- Step 1.3.4: The enlarged set sits inside `F`, so its size is bounded by the size of `F`.
      simpa [hcardInsert] using (Finset.card_le_univ (insert x S))
    -- Step 1.4: Compare the inequality with `card F = 2` to reach the desired contradiction.
    have : (3 : ℕ) ≤ 2 := by simp [hF] at hcontr
    exact (Nat.not_succ_le_self 2 this)
  -- Step 2: Deduce that `1 + 1 = 0`, which will be needed when evaluating the polynomial at `1`.
  have htwo : (1 : F) + 1 = 0 := by
    -- Step 2.1: Apply Step 1 to the element `1 + 1`, so it must be `0` or `1`.
    have hxsum := hx01 ((1 : F) + 1)
    -- Step 2.2: Show that `1 + 1` cannot equal `1`, otherwise we contradict `1 ≠ 0`.
    have hneq : (1 : F) + 1 ≠ 1 := by
      intro h
      have h' : (1 : F) + 1 = (1 : F) + 0 := by
        simpa [add_zero] using h.trans (add_zero (1 : F)).symm
      have : (1 : F) = 0 := add_left_cancel h'
      exact one_ne_zero this
    -- Step 2.3: The only remaining option is `1 + 1 = 0`.
    cases hxsum with
    | inl hzero => exact hzero
    | inr hone => exact (hneq hone).elim
  -- Step 3: Use Step 1 and Step 2 to show that the polynomial has no roots in `F`.
  have hnotroot : ∀ x : F, ¬ IsRoot (X ^ 2 + X + 1 : Polynomial F) x := by
    -- Step 3.1: Any element is either `0` or `1`, so check both cases explicitly.
    intro x
    rcases hx01 x with hx | hx
    · -- Step 3.1.1: Evaluating at `0` yields `1`, so the value cannot be zero.
      subst hx
      simp [IsRoot]
    · -- Step 3.1.2: Evaluating at `1` and using `1 + 1 = 0` again gives the value `1`.
      subst hx
      simp [IsRoot, htwo]
  -- Step 4: Record the degree of `X ^ 2 + 1`, which will help control the degree of the target polynomial.
  have hdeg_base : (X ^ 2 + 1 : Polynomial F).natDegree = 2 := by
    -- Step 4.1: This is a direct application of the degree formula for `X^n + C a` with `n = 2`.
    simpa using (Polynomial.natDegree_X_pow_add_C (R := F) (n := 2) (r := (1 : F)))
  -- Step 5: Note that `X` alone has degree one.
  have hdeg_X : (X : Polynomial F).natDegree = 1 := by
    -- Step 5.1: The standard lemma gives the natural degree of `X`.
    simp [Polynomial.natDegree_X (R := F)]
  -- Step 6: Combine the previous degrees to see that `X` has strictly smaller degree than `X ^ 2 + 1`.
  have hlt :
      (X : Polynomial F).natDegree < (X ^ 2 + 1 : Polynomial F).natDegree := by
    -- Step 6.1: Numerically, this is simply the inequality `1 < 2`.
    simp [hdeg_X, hdeg_base]
  -- Step 7: Compute the exact degree of `X ^ 2 + X + 1` by comparing it with `X ^ 2 + 1`.
  have hdeg : (X ^ 2 + X + 1 : Polynomial F).natDegree = 2 := by
    -- Step 7.1: Rewrite the polynomial as `(X ^ 2 + 1) + X` to use the degree lemma.
    have hrewrite :
        (X ^ 2 + X + 1 : Polynomial F) =
          (X ^ 2 + 1 : Polynomial F) + X := by
      simp [add_comm, add_left_comm]
    -- Step 7.2: Apply the lemma `natDegree_add_eq_left_of_natDegree_lt`.
    calc
      (X ^ 2 + X + 1 : Polynomial F).natDegree
          = ((X ^ 2 + 1 : Polynomial F) + X).natDegree := by simp [hrewrite]
      _ = (X ^ 2 + 1 : Polynomial F).natDegree := by
          simpa using
            (Polynomial.natDegree_add_eq_left_of_natDegree_lt (p := (X ^ 2 + 1 : Polynomial F))
              (q := X) hlt)
      _ = 2 := hdeg_base
  -- Step 8: Encode the fact that the natural degree lies between `1` and `3`, as required by the irreducibility lemma.
  have hdegRange :
      (X ^ 2 + X + 1 : Polynomial F).natDegree ∈ Finset.Icc 1 3 := by
    -- Step 8.1: Because the degree is exactly `2`, membership in the closed interval `[1, 3]` is immediate.
    simp [hdeg]
  -- Step 9: Invoke the general lemma for degrees ≤ 3 together with the “no roots” statement.
  exact Polynomial.irreducible_of_degree_le_three_of_not_isRoot hdegRange hnotroot
