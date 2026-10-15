import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $\Omega=\{1,2,3, \ldots\}$ then $S_{\Omega}$ is an infinite group
-/

/-Informal Proof

Recall that the codomain of an injective function must be at least as large (in cardinality) as the domain of the function. With that in mind, define the function
$$
\begin{gathered}
f: \mathbb{N} \rightarrow S_{\mathbb{N}} \\
f(n)=(1 n)
\end{gathered}
$$
where $(1 n)$ is the cycle decomposition of an element of $S_{\mathbb{N}}$ (specifically it's the function given by $g(1)=n, g(2)=2, g(3)=3, \ldots)$. The function $f$ maps every natural number to a distinct one of these functions. Hence $f$ is injective. Hence $\infty=|\mathbb{N}| \leq\left|S_{\mathbb{N}}\right|$.
-/

theorem Dummit_Foote_exercise_1_3_8 : Infinite (Equiv.Perm ℕ) := by
  -- Step 1: Switch to classical logic so that the permutation simplifications (for swaps) are available.
  classical
  -- Step 2: Define the concrete injection `f` that sends each `n` to the transposition swapping `0` with `n.succ`.
  let f : ℕ → Equiv.Perm ℕ := fun n => Equiv.swap 0 n.succ
  -- Step 3: Prove that `f` is injective by reading off the image of `0`.
  have hf : Function.Injective f := by
    -- Step 3.1: Assume two natural numbers `n` and `m` have the same image under `f`.
    intro n m hnm
    -- Step 3.2: Apply both permutations to `0` to compare the images of that specific element.
    have h_eval : f n 0 = f m 0 := by
      -- Step 3.2.1: Use function extensionality via `congrArg` to evaluate equality at `0`.
      simpa using congrArg (fun g : Equiv.Perm ℕ => g 0) hnm
    -- Step 3.3: Simplify the evaluated equality, which reveals the successors of `n` and `m`.
    have h_succ : n.succ = m.succ := by
      -- Step 3.3.1: Expand `f` and use the swap identities to rewrite both sides explicitly.
      simpa [f, Equiv.swap_apply_def] using h_eval
    -- Step 3.4: Remove the successor constructor to deduce the desired equality `n = m`.
    exact Nat.succ.inj h_succ
  -- Step 4: Invoke the standard criterion that an injective map from the infinite set `ℕ` forces the codomain to be infinite.
  -- Step 4.1: Apply `Infinite.of_injective` with the concrete injection `f`.
  exact Infinite.of_injective (f := f) hf
