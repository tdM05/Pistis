import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that as vector spaces over $\mathbb{Q}, \mathbb{R}^n \cong \mathbb{R}$, for all $n \in \mathbb{Z}^{+}$.
-/

/-Informal Proof

Since $B$ is a basis of $V$, every element of $V$ can be written uniquely as a finite linear combination of elements of $B$. Let $X$ be the set of all such finite linear combinations. Then $X$ has the same cardinality as $V$, since the map from $X$ to $V$ that takes each linear combination to the corresponding element of $V$ is a bijection.

We will show that $X$ has the same cardinality as $B$. Since $B$ is countable and $X$ is a union of countable sets, it suffices to show that each set $X_n$, consisting of all finite linear combinations of $n$ elements of $B$, is countable.

Let $P_n(X)$ be the set of all subsets of $X$ with cardinality $n$. Then we have $X_n \subseteq P_n(B)$. Since $B$ is countable, we have $\mathrm{card}(P_n(B)) \leq \mathrm{card}(B^n) = \mathrm{card}(B)$, where $B^n$ is the Cartesian product of $n$ copies of $B$.

Thus, we have $\mathrm{card}(X_n) \leq \mathrm{card}(P_n(B)) \leq \mathrm{card}(B)$, so $X_n$ is countable. It follows that $X$ is countable, and hence has the same cardinality as $B$.

Therefore, we have shown that the cardinality of $V$ is equal to the cardinality of $B$. Since $F$ is countable, it follows that the cardinality of $V$ is countable as well.

Now let $Q$ be a countable field, and let $R$ be a vector space over $Q$. Let $n$ be a positive integer. Then any basis of $R^n$ over $Q$ has the same cardinality as $R^n$, which is countable. Since $R$ is a direct sum of $n$ copies of $R^n$, it follows that any basis of $R$ over $Q$ has the same cardinality as $R$. Hence, the cardinality of $R$ is countable.

Finally, since $R$ is a countable vector space and $Q$ is a countable field, it follows that $R$ and $Q^{\oplus \mathrm{card}(R)}$ are isomorphic as additive abelian groups. Therefore, we have $R \cong_Q Q^{\oplus \mathrm{card}(R)}$, and in particular $R \cong_Q R^n$ for any positive integer $n$.
-/

theorem Dummit_Foote_exercise_11_1_13 {n : ℕ+} :
  Nonempty ((Fin n → ℝ) ≃ₗ[ℚ] ℝ) := by
  classical
  -- Step 0: unpack `n : ℕ+` to expose the underlying natural number `k` and its positivity.
  rcases n with ⟨k, hk⟩
  -- Step 0.1: rewrite the goal in terms of `k`.
  change Nonempty ((Fin k → ℝ) ≃ₗ[ℚ] ℝ)
  -- Step 1: express the rank of `(Fin k → ℝ)` over `ℚ` using the general `rank_fun` formula.
  have h_rank_fun :
      Module.rank ℚ (Fin k → ℝ) =
        (Fintype.card (Fin k) : Cardinal) * Module.rank ℚ ℝ := by
    -- Step 1.1: instantiate `rank_fun` with `η := Fin k` and `M := ℝ`.
    simp [rank_fun (R := ℚ) (M := ℝ) (η := Fin k)]
  -- Step 2: recall the concrete description of `Module.rank ℚ ℝ` as `Cardinal.continuum`.
  have h_rank_real : Module.rank ℚ ℝ = Cardinal.continuum := Real.rank_rat_real
  -- Step 3: bound the finite cardinal factor by the rank of `ℝ`.
  have h_card_le :
      (Fintype.card (Fin k) : Cardinal) ≤ Module.rank ℚ ℝ := by
    -- Step 3.1: a finite cardinal is strictly less than `ℵ₀`.
    have h_lt_aleph0 :
        (Fintype.card (Fin k) : Cardinal) < Cardinal.aleph0 := by
      -- Step 3.1.1: apply the standard lemma for finite cardinals.
      simp
    -- Step 3.2: combine the previous inequality with `aleph0 ≤ continuum = rank`.
    exact h_lt_aleph0.le.trans
      (by simpa [h_rank_real] using Cardinal.aleph0_le_continuum)
  -- Step 4: show that the finite cardinal factor is nonzero thanks to the positivity of `k`.
  have h_card_ne_zero :
      (Fintype.card (Fin k) : Cardinal) ≠ 0 := by
    -- Step 4.1: exhibit an explicit element of `Fin k` using `hk : 0 < k`.
    have h_nonempty : Nonempty (Fin k) := by
      refine ⟨⟨0, ?_⟩⟩
      simpa using hk
    -- Step 4.2: translate the nonemptiness statement to a nonzero cardinality.
    simpa [Cardinal.mk_fintype] using
      (Cardinal.mk_ne_zero_iff.mpr h_nonempty)
  -- Step 5: collapse the product in `h_rank_fun` using cardinal arithmetic for infinite ranks.
  have h_mul :
      (Fintype.card (Fin k) : Cardinal) * Module.rank ℚ ℝ =
        Module.rank ℚ ℝ := by
    -- Step 5.1: invoke `Cardinal.mul_eq_left`, using that `rank ℚ ℝ` dominates `ℵ₀`.
    have h_aleph0_le : Cardinal.aleph0 ≤ Module.rank ℚ ℝ := by
      -- Step 5.1.1: rewrite with `Cardinal.continuum`.
      simpa [h_rank_real] using Cardinal.aleph0_le_continuum
    -- Step 5.1.2: commute the product to match the goal's orientation.
    simpa [mul_comm] using Cardinal.mul_eq_left h_aleph0_le h_card_le h_card_ne_zero
  -- Step 6: substitute the simplification back into the rank computation.
  have h_rank_eq :
      Module.rank ℚ (Fin k → ℝ) = Module.rank ℚ ℝ := by
    -- Step 6.1: chain the two equalities obtained in Steps 1 and 5.
    exact h_rank_fun.trans h_mul
  -- Step 7: conclude with the classification theorem for vector spaces of equal rank.
  exact nonempty_linearEquiv_of_rank_eq h_rank_eq
