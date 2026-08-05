import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators



/-Informal Statement

Show that every linear map from a one-dimensional vector space to itself is multiplication by some scalar. More precisely, prove that if $\operatorname{dim} V=1$ and $T \in \mathcal{L}(V, V)$, then there exists $a \in \mathbf{F}$ such that $T v=a v$ for all $v \in V$.
-/

/-Informal Proof

If $\operatorname{dim} V=1$, then in fact, $V=\mathbf{F}$ and it is spanned by $1 \in \mathbf{F}$.
Let $T$ be a linear map from $V$ to itself. Let $T(1)=\lambda \in V(=\mathbf{F})$.
Step 2
2 of 3
Every $v \in V$ is a scalar. Therefore,
$$
\begin{aligned}
T(v) & =T(v \cdot 1) \\
& =v T(1) \ldots .(\text { By the linearity of } T) \\
& =v \lambda
\end{aligned}
$$
Hence, $T v=\lambda v$ for every $v \in V$.
-/

theorem Axler_exercise_3_1 {F V : Type*}
  [AddCommGroup V] [Field F] [Module F V] [FiniteDimensional F V]
  (T : V →ₗ[F] V) (hT : finrank F V = 1) :
  ∃ c : F, ∀ v : V, T v = c • v:= by
  -- Step 1: Work in the classical logic universe so that we can choose concrete witnesses.
  classical
  -- Step 2: Extract a specific nonzero vector witnessing that the finrank is positive.
  have hpos : 0 < finrank F V := by
    -- Step 2.1: The hypothesis `finrank F V = 1` implies positivity directly.
    simp [hT]
  -- Step 2.2: Turn the positivity statement into the existence of a nonvanishing vector.
  obtain ⟨x, hx⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := F) (M := V)).1 hpos
  -- Step 3: Because the space is one-dimensional, `T x` must be a scalar multiple of `x`.
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_finrank_eq_one (K := F) (V := V) (x := x) hT hx (T x)
  -- Step 4: Show that the same scalar `c` works for every vector of the space.
  refine ⟨c, ?_⟩
  -- Step 4.1: Fix an arbitrary vector and express it as a scalar multiple of `x`.
  intro v
  -- Step 4.1.1: Use the one-dimensionality lemma again to write `v = a • x`.
  obtain ⟨a, ha⟩ :=
    exists_smul_eq_of_finrank_eq_one (K := F) (V := V) (x := x) hT hx v
  -- Step 4.2: Transport the equality `v = a • x` through the linear map and compare both sides.
  calc
    T v = T (a • x) := by
      -- Step 4.2.1: Replace `v` with its scalar-multiple representation.
      simp [ha]
    _ = a • T x := by
      -- Step 4.2.2: A linear map respects scalar multiplication.
      simp
    _ = a • (c • x) := by
      -- Step 4.2.3: Substitute the defining relation for `c`.
      simp [hc]
    _ = (a * c) • x := by
      -- Step 4.2.4: Collapse the nested scalar multiplication.
      simpa [mul_comm, mul_left_comm, mul_assoc] using (smul_smul a c x)
    _ = (c * a) • x := by
      -- Step 4.2.5: Commute the scalars inside the product (the field multiplication is commutative).
      simp [mul_comm]
    _ = c • (a • x) := by
      -- Step 4.2.6: Expand the product back into iterated scalar multiplication.
      simpa [mul_comm, mul_left_comm, mul_assoc] using (smul_smul c a x).symm
    _ = c • v := by
      -- Step 4.2.7: Return to the original expression for `v`.
      simp [ha]
