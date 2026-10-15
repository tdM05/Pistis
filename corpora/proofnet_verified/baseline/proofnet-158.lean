import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Prove that in $\mathbb{C}$, convergence of $\left\{s_{n}\right\}$ implies convergence of $\left\{\left|s_{n}\right|\right\}$.
-/

/-Informal Proof

Let $\varepsilon>0$. Since the sequence $\left\{s_n\right\}$ is a Cauchy sequence, there exists $N$ such that $\left|s_m-s_n\right|<\varepsilon$ for all $m>N$ and $n>N$. We then have $\left| |s_m| - |s_n| \right| \leq\left|s_m-s_n\right|<\varepsilon$ for all $m>N$ and $n>N$. Hence the sequence $\left\{\left|s_n\right|\right\}$ is also a Cauchy sequence, and therefore must converge.
-/

theorem Rudin_exercise_3_1a
  (f : ℕ → ℝ)
  (h : ∃ (a : ℝ), Tendsto (λ (n : ℕ) => f n) atTop (𝓝 a))
  : ∃ (a : ℝ), Tendsto (λ (n : ℕ) => |f n|) atTop (𝓝 a) := by
  -- Step 1: Extract the specific real number `a` so that `f n → a`.
  rcases h with ⟨a, ha⟩
  -- Step 2: Declare the candidate limit for `|f n|`, namely `|a|`.
  refine ⟨|a|, ?_⟩
  -- Step 3: Capture the fact that the absolute value function is continuous at `a`.
  have h_abs :
      Tendsto (fun x : ℝ => |x|) (𝓝 a) (𝓝 |a|) := by
    -- Step 3.1: Apply the built-in lemma `continuous_abs.tendsto` to obtain this limit.
    simpa using continuous_abs.tendsto a
  -- Step 4: Compose the convergence of `f` with the convergence of the absolute value function.
  have h_comp :
      Tendsto (fun n => |f n|) atTop (𝓝 |a|) := by
    -- Step 4.1: Use `Tendsto.comp` and unfold the composition to match our goal.
    simpa [Function.comp] using h_abs.comp ha
  -- Step 5: Finish by returning the composed limit.
  exact h_comp

/-
Corrected formulation (faithful):

Rudin's exercise 3.1(a) is stated for sequences $\{s_n\}$ where $|\cdot|$
denotes the modulus — Rudin Chapter 3 introduces sequences in both $\mathbb{R}$
and $\mathbb{C}$, and the natural reading takes $s_n \in \mathbb{C}$.  The
original Lean statement above artificially restricts to `ℕ → ℝ`, which is
strictly weaker than the natural-language claim.  The corrected version uses
`ℕ → ℂ` and takes `|·|` to be the norm (= modulus) on `ℂ`.
-/

theorem Rudin_exercise_3_1a_corrected
  (f : ℕ → ℂ)
  (h : ∃ (a : ℂ), Tendsto (λ (n : ℕ) => f n) atTop (𝓝 a))
  : ∃ (a : ℝ), Tendsto (λ (n : ℕ) => ‖f n‖) atTop (𝓝 a) := by
  -- Step 1: Extract the specific complex limit `a` from the hypothesis.
  rcases h with ⟨a, ha⟩
  -- Step 2: Declare the candidate real limit for `‖f n‖`, namely `‖a‖`.
  refine ⟨‖a‖, ?_⟩
  -- Step 3: The norm map `‖·‖ : ℂ → ℝ` is continuous, hence sequentially continuous at `a`.
  have h_norm :
      Tendsto (fun x : ℂ => ‖x‖) (𝓝 a) (𝓝 ‖a‖) :=
    continuous_norm.tendsto a
  -- Step 4: Compose the convergence of `f` with continuity of the norm.
  simpa [Function.comp] using h_norm.comp ha
