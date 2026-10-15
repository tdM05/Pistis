import Mathlib

open Filter Real Function
open scoped Topology



/-Informal Statement

Show that every subset of $\mathbb{N}$ is clopen.
-/

/-Informal Proof

32. The one-point set $\{n\} \subset \mathbb{N}$ is open, since it contains all $m \in \mathbb{N}$ that satisfy $d(m, n)<\frac{1}{2}$. Every subset of $\mathbb{N}$ is a union of one-point sets, hence is open. Then every set it closed, since its complement is necessarily open.
-/

theorem Pugh_exercise_2_32a (A : Set ℕ) : IsClopen A := by
  -- Step 1: Invoke the fact that ℕ carries the discrete topology, so every subset is both open
  --         and closed; the lemma `isClopen_discrete` packages this information for any set.
  -- Step 1.1: Specialize `isClopen_discrete` to the particular subset `A : Set ℕ`.
  -- Step 2: Apply that lemma directly to conclude that `A` is clopen.
  exact isClopen_discrete (X := ℕ) A
