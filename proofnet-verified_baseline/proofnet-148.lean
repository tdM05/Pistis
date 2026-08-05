import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

If $r$ is rational $(r \neq 0)$ and $x$ is irrational, prove that $r+x$ is irrational.
-/

/-Informal Proof

If $r$ and $r+x$ were both rational, then $x=r+x-r$ would also be rational.
-/

theorem Rudin_exercise_1_1a
  (x : ℝ) (y : ℚ) (hy : y ≠ 0) :
  ( Irrational x ) -> Irrational ( x + y ) := by
  -- Step 1: Introduce the hypothesis that `x` is irrational.
  intro hx
  -- Step 1.1: Note the non-zero assumption on `y` so that every given hypothesis is acknowledged.
  have _hy : y ≠ 0 := hy
  -- Step 2: Unfold the definition of irrationality so that we can work directly with rational witnesses.
  dsimp [Irrational] at hx ⊢
  -- Step 3: Assume, aiming for a contradiction, that `x + y` is rational.
  intro hxy
  -- Step 3.1: Extract the rational number `q` whose real value equals `x + y`.
  rcases hxy with ⟨q, hq⟩
  -- Step 4: Use the irrationality of `x` to reach a contradiction by exhibiting a rational expression for `x`.
  apply hx
  -- Step 4.1: Propose `q - y` (which is rational) as the witness that would force `x` to be rational.
  refine ⟨q - y, ?_⟩
  -- Step 4.2: Relate the real casting of `q - y` with the subtraction of their real casts.
  have hcast : ((q - y : ℚ) : ℝ) = (q : ℝ) - y := by
    -- Step 4.2.1: Casting from ℚ to ℝ commutes with subtraction, so we can push the cast inside.
    norm_cast
  -- Step 4.3: Subtract `y` from both sides of the equation `(q : ℝ) = x + y` to isolate `x`.
  have hsubtract : (q : ℝ) - y = x := by
    -- Step 4.3.1: Apply the function `t ↦ t - y` to both sides of `hq`.
    have := congrArg (fun t : ℝ => t - y) hq
    -- Step 4.3.2: Simplify the right-hand side to get rid of `+ y` and `- y`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Step 4.4: Combine the previous two equalities to conclude that the real cast of `q - y` equals `x`.
  simpa using hcast.trans hsubtract
