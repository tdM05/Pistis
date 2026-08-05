import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $u$ is a unit in $R$ then so is $-u$.
-/

/-Informal Proof

Solution: Since $u$ is a unit, we have $u v=v u=1$ for some $v \in R$. Thus, we have
$$
(-v)(-u)=v u=1
$$
and
$$
(-u)(-v)=u v=1 .
$$
Thus $-u$ is a unit.
-/

theorem Dummit_Foote_exercise_7_1_2 {R : Type*} [Ring R] {u : R}
  (hu : IsUnit u) : IsUnit (-u) := by
  -- Step 1: Unpack the datum that `u` is a unit into an explicit witness `u' : Units R`
  --         whose underlying value equals `u`.
  rcases hu with ⟨u', rfl⟩
  -- Step 2: Observe that units are closed under negation, so `-u'` is also a unit of `R`.
  refine ⟨-u', ?_⟩
  -- Step 3: Check that the underlying element of `-u'` is exactly `-u`, which now equals `-↑u'`.
  --         This follows from how negation is defined on `Units R`.
  simp
