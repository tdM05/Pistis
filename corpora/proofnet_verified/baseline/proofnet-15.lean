import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators



/-Informal Statement

Prove that $-(-v) = v$ for every $v \in V$.
-/

/-Informal Proof

By definition, we have
$$
(-v)+(-(-v))=0 \quad \text { and } \quad v+(-v)=0 .
$$
This implies both $v$ and $-(-v)$ are additive inverses of $-v$, by the uniqueness of additive inverse, it follows that $-(-v)=v$.
-/

theorem Axler_exercise_1_3 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {v : V} : -(-v) = v := by
  /- Step 1: Recognize that the desired identity is precisely the lemma `neg_neg`. -/
  /- Step 1.1: Invoke `simp`, whose rewriting table contains `neg_neg`, to rewrite `-(-v)` into `v`. -/
  simp
