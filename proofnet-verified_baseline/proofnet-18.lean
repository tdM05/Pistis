import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators



/-Informal Statement

Suppose $p \in \mathcal{P}(\mathbf{C})$ has degree $m$. Prove that $p$ has $m$ distinct roots if and only if $p$ and its derivative $p^{\prime}$ have no roots in common.
-/

/-Informal Proof

First, let $p$ have $m$ distinct roots. Since $p$ has the degree of $m$, then this could imply that $p$ can be actually written in the form of $p(z)=c\left(z-\lambda_1\right) \ldots\left(z-\lambda_m\right)$, which you have $\lambda_1, \ldots, \lambda_m$ being distinct.
To prove that both $p$ and $p^{\prime}$ have no roots in commons, we must now show that $p^{\prime}\left(\lambda_j\right) \neq 0$ for every $j$. So, to do so, just fix $j$. The previous expression for $p$ shows that we can now write $p$ in the form of $p(z)=\left(z-\lambda_j\right) q(z)$, which $q$ is a polynomial such that $q\left(\lambda_j\right) \neq 0$.

When you differentiate both sides of the previous equation, then you would then have $p^{\prime}(z)=(z-$ $\left.\lambda_j\right) q^{\prime}(z)+q(z)$

Therefore: $\left.=p^{\prime}\left(\lambda_j\right)=q \lambda_j\right)$
Equals: $p^{\prime}\left(\lambda_j\right) \neq 0$

Now, to prove the other direction, we would now prove the contrapositive, which means that we will be proving that if $p$ has actually less than $m$ distinct roots, then both $p$ and $p^{\prime}$ have at least one root in common.

Now, for some root of $\lambda$ of $p$, we can write $p$ is in the form of $\left.p(z)=(z-\lambda)^n q(z)\right)$, which is where both $n \geq 2$ and $q$ is a polynomial. When differentiating both sides of the previous equations, we would then have $p^{\prime}(z)=(z-\lambda)^n q^{\prime}(z)+n(z-\lambda)^{n-1} q(z)$.
Therefore, $p^{\prime}(\lambda)=0$, which would make $\lambda$ is a common root of both $p$ and $p^{\prime}$.
-/

theorem Axler_exercise_4_4 (p : Polynomial ℂ) :
  p.degree = @card (rootSet p ℂ) (rootSetFintype p ℂ) ↔
  Disjoint
  (@card (rootSet (derivative p) ℂ) (rootSetFintype (derivative p) ℂ))
  (@card (rootSet p ℂ) (rootSetFintype p ℂ)) := by
  sorry

/-
Step 1: Observe that the codomain of `Disjoint` in the original statement is `ℕ`, because
        both arguments are the cardinals of root sets.
Step 2: Realize that `Disjoint` on natural numbers means `min m n = 0`, so at least one
        of the numbers must be zero.
Step 3: Choose the concrete polynomial `q(z) = z^2 - 1`.  This polynomial has degree `2`
        and exactly two distinct complex roots (`{-1, 1}`), hence the left-hand side of
        the stated equivalence is true for `q`.
Step 4: Compute the derivative `q' = 2z`, whose complex root set is `{0}` and therefore
        has cardinality `1`.  Consequently the right-hand side reduces to `Disjoint 1 2`,
        which is false because `min 1 2 = 1`.
Step 5: Conclude that the stated equivalence fails for `q`, so the original theorem is
        false as written: its left-hand side can be true while the right-hand side is
        false.

The original formalization is just simply wrong!
The right side talks about disjoint numbers instead of sets: Disjoint should compare sets/finsets of roots, not their cardinalities. Saying two Nats are Disjoint doesn't even make sense here, and is not consistent with the natural language statement.
-/

theorem Axler_exercise_4_4_neg :
    ¬
      (∀ p : Polynomial ℂ,
        p.degree = @card (rootSet p ℂ) (rootSetFintype p ℂ) ↔
          Disjoint
            (@card (rootSet (derivative p) ℂ) (rootSetFintype (derivative p) ℂ))
            (@card (rootSet p ℂ) (rootSetFintype p ℂ))) := by
  classical
  -- Step 1: Fix the counterexample polynomial `q(z) = z^2 - 1`.
  intro h
  -- Step 2: Introduce the concrete polynomial and record its basic data.
  set q : Polynomial ℂ := Polynomial.X ^ 2 - 1
  have hq_deg : q.degree = (2 : WithTop ℕ) := by
    -- Step 2.1: Use the dedicated lemma for the degree of `X^2 - C 1`.
    simpa [q] using
      (Polynomial.degree_X_pow_sub_C (R := ℂ) (n := 2) (a := (1 : ℂ))
        (by decide : 0 < (2 : ℕ)))
  have hq_natDeg :
      Fintype.card (q.rootSet ℂ) = 2 := by
    -- Step 3.1: `q` is separable and splits, so its distinct roots reach its degree.
    have hq_sep :
        q.Separable := by
      -- Step 3.1.1: Apply the separability lemma for `X^n - a` with `n = 2`, `a = 1`.
      simpa [q] using
        (Polynomial.separable_X_pow_sub_C (F := ℂ) (n := 2) (a := (1 : ℂ))
          (by
            -- Step 3.1.1.1: Show that `2` is nonzero in the complex numbers.
            simp)
          (by
            -- Step 3.1.1.2: Confirm that the constant `1` is nonzero in ℂ.
            simp))
    have hq_split :
        (q.map (algebraMap ℂ ℂ)).Splits :=
      -- Step 3.1.2: Any polynomial with complex coefficients splits over ℂ.
      IsAlgClosed.splits_domain q
    have hq_nat :
        q.natDegree = 2 := by
      -- Step 3.1.3: Record the natural degree of `q`.
      simpa [q] using
        (Polynomial.natDegree_X_pow_sub_C (R := ℂ) (n := 2) (r := (1 : ℂ)))
    -- Step 3.2: Convert the general cardinality lemma to the concrete value `2`.
    simpa [hq_nat] using
      (Polynomial.card_rootSet_eq_natDegree hq_sep hq_split)
  have hq_card :
      @card (q.rootSet ℂ) (rootSetFintype q ℂ) = 2 := by
    -- Step 4: Translate the finite-type cardinal into the explicit natural number.
    simpa using hq_natDeg
  have hq_derivative :
      Polynomial.derivative q = Polynomial.C (2 : ℂ) * Polynomial.X := by
    -- Step 5: Differentiate `q` explicitly.
    have hpow :
        Polynomial.derivative (Polynomial.X ^ 2 : Polynomial ℂ) =
          Polynomial.C (2 : ℂ) * Polynomial.X := by
      -- Step 5.1: Use the closed form for the derivative of a monomial.
      simpa using
        (Polynomial.derivative_X_pow (R := ℂ) (n := 2))
    simp [q, hpow]
  have hq_deriv_root :
      (Polynomial.derivative q).rootSet ℂ = ({0} : Set ℂ) := by
    -- Step 6: Use the root-set lemma for `C a * X^n` with `n = 1`, `a = 2`.
    simpa [hq_derivative] using
      (Polynomial.rootSet_C_mul_X_pow (R := ℂ) (S := ℂ) (n := 1) (a := (2 : ℂ))
        (by decide : (1 : ℕ) ≠ 0)
        (by
          -- Step 6.1: The leading coefficient `2` is nonzero.
          simp))
  have hq_deriv_card :
      @card ((Polynomial.derivative q).rootSet ℂ)
          (rootSetFintype (Polynomial.derivative q) ℂ) = 1 := by
    -- Step 7: Turn the singleton description into its cardinality.
    classical
    -- Step 7.1: The derivative is nonzero so that we can inhabit the root set.
    have hderiv_ne_zero :
        Polynomial.derivative q ≠ 0 := by
      -- A product of two nonzero polynomials is nonzero.
      simp [hq_derivative]
    -- Step 7.2: Exhibit `0` as the unique element of the root set.
    have hzero :
        (0 : ℂ) ∈ (Polynomial.derivative q).rootSet ℂ :=
      (Polynomial.mem_rootSet_of_ne (S := ℂ)
            (p := Polynomial.derivative q) hderiv_ne_zero).2
        (by
          -- Evaluating `C 2 * X` at `0` gives `0`.
          simp [hq_derivative])
    -- Step 7.3: Any root must coincide with `0`, yielding a singleton type.
    refine (Fintype.card_eq_one_iff.mpr ?_)
    refine ⟨⟨0, hzero⟩, ?_⟩
    intro y
    cases' y with z hz
    -- Step 7.4: Membership in `{0}` forces equality with `0`.
    have hz' : z = 0 := by
      have : z ∈ ({0} : Set ℂ) := by simpa [hq_deriv_root] using hz
      simpa using this
    -- Step 7.5: Conclude the equality in the subtype.
    apply Subtype.ext
    simp [hz']
  -- Step 8: Compile the left-hand side of the claimed equivalence for `q`.
  have h_left :
      q.degree =
        @card (q.rootSet ℂ) (rootSetFintype q ℂ) := by
    -- Step 8.1: Both sides are `2`, so the equality is immediate.
    simp [hq_deg, hq_card]
  -- Step 9: Invoke the assumed equivalence on `q`.
  have h_disjoint :
      Disjoint
        (@card ((Polynomial.derivative q).rootSet ℂ)
            (rootSetFintype (Polynomial.derivative q) ℂ))
        (@card (q.rootSet ℂ) (rootSetFintype q ℂ)) :=
    (h q).1 h_left
  -- Step 10: Simplify the `Disjoint` statement to `Disjoint 1 2`, which is false.
  have h_disjoint_false :
      ¬
        Disjoint
          (@card ((Polynomial.derivative q).rootSet ℂ)
              (rootSetFintype (Polynomial.derivative q) ℂ))
          (@card (q.rootSet ℂ) (rootSetFintype q ℂ)) := by
    -- Step 10.1: `Disjoint 1 2` fails because their infimum is not `0`.
    intro h'
    have hmin0 :
        ((@card ((Polynomial.derivative q).rootSet ℂ)
              (rootSetFintype (Polynomial.derivative q) ℂ))
          ⊓
          (@card (q.rootSet ℂ) (rootSetFintype q ℂ))) = 0 :=
      Disjoint.eq_bot h'
    have : (1 : ℕ) ⊓ 2 ≠ 0 := by
      -- The infimum of two positive naturals is strictly positive.
      simp
    exact this (by simp [hq_deriv_card, hq_card] at hmin0)
  -- Step 11: Derive the contradiction.
  exact h_disjoint_false h_disjoint

private lemma degree_eq_card_rootSet_iff_separable
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    p.degree =
        @card (p.rootSet ℂ) (rootSetFintype p ℂ) ↔
      p.Separable := by
  classical
  -- Step 1: Record that every complex polynomial splits over ℂ.
  have hsplit :
      (p.map (algebraMap ℂ ℂ)).Splits :=
    IsAlgClosed.splits_domain p
  constructor
  · -- Step 2: Assume the degree equals the cardinality and deduce separability.
    intro hdeg
    -- Step 2.1: Move to natural degrees using `degree_eq_natDegree`.
    have h_withTop :
        (p.natDegree : WithTop ℕ) =
          (@card (p.rootSet ℂ) (rootSetFintype p ℂ) : WithTop ℕ) := by
      simpa [Polynomial.degree_eq_natDegree hp] using hdeg
    -- Step 2.2: Extract the plain natural-number equality.
    have h_nat :
        Fintype.card (p.rootSet ℂ) = p.natDegree :=
      (WithTop.coe_eq_coe.mp h_withTop).symm
    -- Step 2.3: Apply the standard cardinality-versus-separability equivalence.
    exact
      (Polynomial.card_rootSet_eq_natDegree_iff_of_splits
          (F := ℂ) (K := ℂ) (f := p) hp hsplit).mp h_nat
  · -- Step 3: Show that separability forces the cardinality/degree equality.
    intro hsep
    -- Step 3.1: Use the same lemma in the forward direction.
    have h_nat :
        Fintype.card (p.rootSet ℂ) = p.natDegree :=
      (Polynomial.card_rootSet_eq_natDegree_iff_of_splits
          (F := ℂ) (K := ℂ) (f := p) hp hsplit).mpr hsep
    -- Step 3.2: Lift the natural-number equality back to `WithTop`.
    have h_withTop :
        (@card (p.rootSet ℂ) (rootSetFintype p ℂ) : WithTop ℕ) =
          (p.natDegree : WithTop ℕ) :=
      by simpa using congrArg (fun n : ℕ => (n : WithTop ℕ)) h_nat
    -- Step 3.3: Translate `natDegree` into `degree`.
    simp [Polynomial.degree_eq_natDegree hp, h_withTop]

private lemma separable_iff_root_sets_disjoint
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    p.Separable ↔
      Disjoint (p.rootSet ℂ) ((Polynomial.derivative p).rootSet ℂ) := by
  classical
  constructor
  · -- Step 1: Prove that separability forbids common roots.
    intro hsep
    -- Step 1.1: Use the characterization of disjointness via membership.
    refine Set.disjoint_left.2 ?_
    intro z hz hz'
    -- Step 1.2: Convert set membership to the statement that `z` is a root.
    have hz_root :
        p.IsRoot z :=
      by
        -- Step 1.2.1: Evaluate the polynomial at the root via `mem_rootSet_of_ne`.
        have hz_eval :=
          (Polynomial.mem_rootSet_of_ne (S := ℂ) (p := p) hp).1 hz
        simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hz_eval
    have hz'_root :
        (Polynomial.derivative p).IsRoot z :=
      by
        -- Step 1.2.2: Establish that the derivative is nonzero at the root.
        have hderiv_ne :
            Polynomial.derivative p ≠ 0 :=
          by
            -- If the derivative vanished, its root set would be empty.
            intro hzero
            have : z ∈ (Polynomial.derivative p).rootSet ℂ := hz'
            simp [hzero, Polynomial.rootSet_zero] at this
        -- Step 1.2.3: Evaluate the derivative at the root.
        have hz_eval :=
          (Polynomial.mem_rootSet_of_ne
              (S := ℂ) (p := Polynomial.derivative p) hderiv_ne).1 hz'
        simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hz_eval
    -- Step 1.3: Translate the simultaneous roots into multiplicity information.
    have hmult :
        1 < p.rootMultiplicity z :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot (p := p) (t := z) hp).2
        ⟨hz_root, hz'_root⟩
    -- Step 1.4: Separability forces every root multiplicity to be ≤ 1, contradiction.
    have h_le_one :=
      Polynomial.rootMultiplicity_le_one_of_separable hsep z
    have hcontr := lt_of_lt_of_le hmult h_le_one
    exact (lt_irrefl (1 : ℕ)) hcontr
  · -- Step 2: Show that disjoint root sets imply separability.
    intro hdis
    -- Step 2.1: Prove the contrapositive by assuming `p` is not separable.
    by_contra hsep
    have hnotcoprime :
        ¬ IsCoprime p (Polynomial.derivative p) := by
      -- Step 2.1.1: Unfold the definition of separability.
      simpa [Polynomial.Separable] using hsep
    -- Step 2.2: Define the gcd of `p` and its derivative.
    set g : Polynomial ℂ := EuclideanDomain.gcd p (Polynomial.derivative p)
    -- Step 2.3: Record that the gcd is not a unit (else the polynomials are coprime).
    have hg_not_unit :
        ¬IsUnit g :=
      by
        have : IsUnit g ↔ IsCoprime p (Polynomial.derivative p) :=
          by
            simpa [g] using
              (EuclideanDomain.gcd_isUnit_iff
                (α := Polynomial ℂ) (x := p)
                (y := Polynomial.derivative p))
        exact (not_congr this).mpr hnotcoprime
    -- Step 2.4: Show that the gcd is nonzero, since it divides the nonzero polynomial `p`.
    have hg_ne_zero : g ≠ 0 := by
      intro hg
      have hg_dvd :
          g ∣ p :=
        EuclideanDomain.gcd_dvd_left p (Polynomial.derivative p)
      obtain ⟨q, hq⟩ := hg_dvd
      have : p = 0 := by simpa [g, hg] using hq
      exact hp this
    -- Step 2.5: A non-unit polynomial in `ℂ[X]` must have positive degree.
    have hg_deg_ne_zero :
        g.degree ≠ 0 :=
      by
        intro hdeg
        have : IsUnit g :=
          (Polynomial.isUnit_iff_degree_eq_zero).2 hdeg
        exact hg_not_unit this
    -- Step 2.6: Because ℂ is algebraically closed, the gcd has a complex root.
    obtain ⟨z, hz⟩ :=
      IsAlgClosed.exists_root (p := g) hg_deg_ne_zero
    -- Step 2.7: Convert this root of the gcd into roots of `p` and its derivative.
    have hz_root : p.IsRoot z := by
      -- `g` divides `p`, so any root of `g` is a root of `p`.
      exact hz.dvd (EuclideanDomain.gcd_dvd_left p (Polynomial.derivative p))
    have hz_deriv_root : (Polynomial.derivative p).IsRoot z := by
      -- `g` also divides the derivative, giving the second root condition.
      exact hz.dvd (EuclideanDomain.gcd_dvd_right p (Polynomial.derivative p))
    -- Step 2.8: Deduce that the root has multiplicity strictly greater than `1`.
    have hmult :
        1 < p.rootMultiplicity z :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot
          (p := p) (t := z) hp).2 ⟨hz_root, hz_deriv_root⟩
    -- Step 2.9: Upgrade the `IsRoot` statements to membership in the respective root sets.
    have hz_eval : Polynomial.eval z p = 0 := hz_root.eq_zero
    have hz_mem :
        z ∈ p.rootSet ℂ :=
      (Polynomial.mem_rootSet_of_ne (S := ℂ) (p := p) hp).2
        (by
          -- Convert evaluation into the `aeval` formulation (which coincides with evaluation).
          simpa using hz_eval)
    have hz_deriv_eval :
        Polynomial.eval z (Polynomial.derivative p) = 0 :=
      hz_deriv_root.eq_zero
    have hderiv_ne :
        Polynomial.derivative p ≠ 0 :=
      by
        intro hzero
        have hp_const :
            p = Polynomial.C (Polynomial.coeff p 0) :=
          Polynomial.eq_C_of_derivative_eq_zero hzero
        have hcoeff_zero :
            Polynomial.coeff p 0 = 0 := by
          -- Evaluate the constant polynomial at the repeated root.
          have hz_const := hz_eval
          -- Rewrite the evaluation of the constant polynomial explicitly.
          rw [hp_const, Polynomial.eval_C] at hz_const
          simpa using hz_const
        have hp_zero : p = 0 := by
          -- Replace the constant polynomial with the zero polynomial.
          have hp_C0 : p = Polynomial.C 0 := by
            simpa [hcoeff_zero] using hp_const
          simpa [Polynomial.C_0] using hp_C0
        exact hp hp_zero
    have hz_mem_deriv :
        z ∈ (Polynomial.derivative p).rootSet ℂ :=
      (Polynomial.mem_rootSet_of_ne (S := ℂ)
          (p := Polynomial.derivative p) hderiv_ne).2
        (by
          -- Convert the evaluation of the derivative to the `aeval` format.
          simpa using hz_deriv_eval)
    -- Step 2.10: The disjointness hypothesis forbids such a common root.
    exact
      (Set.disjoint_left.mp hdis hz_mem hz_mem_deriv)

/-
Implicit Premise: (hp : p ≠ 0)

If p = 0, then p.rootSet ℂ = ∅ by Mathlib/Algebra/Polynomial/Roots.lean:506, so card (p.rootSet ℂ) = 0 and the left side becomes ⊥ = 0, which is false because Polynomial.degree 0 = ⊥.
Polynomial.derivative p = 0, so the right side is Disjoint ∅ ∅, which is false.
-/
theorem Axler_exercise_4_4_corrected (p : Polynomial ℂ) (m : ℕ) (hp : p ≠ 0) (hm : m = p.degree) :
    @card (p.rootSet ℂ) (rootSetFintype p ℂ) = m ↔
    Disjoint (p.rootSet ℂ) ((Polynomial.derivative p).rootSet ℂ) := by
  -- Step 0: Switch to classical logic so that all cardinality lemmas are directly available.
  classical
  -- Step 1: Combine the standard Mathlib equivalences that translate the equality of degrees
  --         into separability and finally into disjoint root sets.
  have h :=
    (degree_eq_card_rootSet_iff_separable p hp).trans
      (separable_iff_root_sets_disjoint p hp)
  -- Step 2: Prove the forward direction of the equivalence.
  constructor
  · intro hcard
    -- Step 2.1: Lift the natural-number equality to `WithTop ℕ`, matching the codomain of `degree`.
    have hcard_coe :
        ((@card (p.rootSet ℂ) (rootSetFintype p ℂ) : ℕ) : WithTop ℕ) = m :=
      congrArg (fun n : ℕ => (n : WithTop ℕ)) hcard
    -- Step 2.2: Use `hm` to rewrite the degree equality so it matches the shape expected by `h`.
    have hdeg :
        p.degree =
          ((@card (p.rootSet ℂ) (rootSetFintype p ℂ) : ℕ) : WithTop ℕ) := by
      simpa [hcard_coe] using hm.symm
    -- Step 2.3: Apply the composed equivalence to obtain the disjointness statement.
    exact h.mp hdeg
  · intro hdis
    -- Step 3: Prove the reverse direction of the equivalence.
    -- Step 3.1: Push the disjointness hypothesis through the equivalence `h` to recover the
    --           degree/cardinality equality in `WithTop ℕ`.
    have hdeg :
        p.degree =
          ((@card (p.rootSet ℂ) (rootSetFintype p ℂ) : ℕ) : WithTop ℕ) :=
      h.mpr hdis
    -- Step 3.2: Combine the result with `hm` to compare the coerced natural numbers.
    have hcoe :
        (m : WithTop ℕ) =
          ((@card (p.rootSet ℂ) (rootSetFintype p ℂ) : ℕ) : WithTop ℕ) :=
      hm.trans hdeg
    -- Step 3.3: Remove the coercions, giving the pure natural-number equality.
    have hm_nat :
        m = @card (p.rootSet ℂ) (rootSetFintype p ℂ) :=
      WithTop.coe_eq_coe.mp hcoe
    -- Step 3.4: Reorient the equality to match the statement of the theorem.
    exact hm_nat.symm
