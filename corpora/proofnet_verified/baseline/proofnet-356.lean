import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Suppose $g$ is a real function on $R^{1}$, with bounded derivative (say $\left|g^{\prime}\right| \leq M$ ). Fix $\varepsilon>0$, and define $f(x)=x+\varepsilon g(x)$. Prove that $f$ is one-to-one if $\varepsilon$ is small enough.
-/

/-Informal Proof

If $0<\varepsilon<\frac{1}{M}$, we certainly have
$$
f^{\prime}(x) \geq 1-\varepsilon M>0,
$$
and this implies that $f(x)$ is one-to-one, by the preceding problem.
-/

theorem Rudin_exercise_5_3 {g : ℝ → ℝ} (hg : Continuous g)
  (hg' : ∃ M : ℝ, ∀ x : ℝ, |deriv g x| ≤ M) :
  ∃ N, ∀ ε > 0, ε < N → Function.Injective (λ x : ℝ => x + ε * g x) := by
  sorry

/-
The statement above is mathematically correct, but the proof in Lean needs the
(implicit) premise that `g` is differentiable everywhere so that `deriv g x`
really refers to the derivative of `g`.  We add this missing hypothesis in a
corrected version and carry out the detailed argument.

The formalization also silently uses the mean value theorem, which requires a
genuine derivative bound.  If we drop that derivative control and only assume
continuity, the conclusion fails: the quadratic function `g x = x ^ 2` gives a
family `x ↦ x + ε x ^ 2` that is never injective because
`f 0 = f (-1/ε) = 0` for every positive `ε`.  The next lemma packages that
counterexample as the negation of the weakened, purely continuous variant.
-/

/-!
The negation: continuity alone does not force injectivity of
`x ↦ x + ε g x` for small `ε`.
-/
theorem Rudin_exercise_5_3_neg :
  ∃ g : ℝ → ℝ,
    Continuous g ∧
      (∀ N > 0, ∃ ε > 0, ε < N ∧ ¬ Function.Injective (fun x : ℝ => x + ε * g x)) := by
  classical
  -- Step 1: choose the counterexample `g x = x^2`.
  refine ⟨fun x : ℝ => x ^ 2, ?_, ?_⟩
  · -- Step 1.1: polynomial functions are continuous.
    simpa using (continuous_id.pow 2)
  · -- Step 2: for any positive `N`, produce a positive `ε < N` that breaks injectivity.
    intro N hNpos
    -- Step 2.1: pick `ε = (min N 1) / 2` so that `0 < ε < N`.
    set ε : ℝ := (min N 1) / 2 with hεdef
    -- Split on whether `N ≤ 1` to control the simple fraction estimates.
    have hεpos : 0 < ε := by
      by_cases hNle1 : N ≤ 1
      · -- here `ε = N/2`
        have hrewrite : ε = N / 2 := by
          have : min N 1 = N := min_eq_left hNle1
          simp [hεdef, this]
        nlinarith
      · -- here `N > 1`, so `ε = 1/2`
        have hNgt1 : 1 < N := lt_of_not_ge hNle1
        have hrewrite : ε = (1 : ℝ) / 2 := by
          have : min N 1 = 1 := min_eq_right (le_of_lt hNgt1)
          simp [hεdef, this]
        nlinarith
    have hεltN : ε < N := by
      by_cases hNle1 : N ≤ 1
      · -- then `ε = N/2`
        have hrewrite : ε = N / 2 := by
          have : min N 1 = N := min_eq_left hNle1
          simp [hεdef, this]
        have hNpos' : 0 < N := hNpos
        nlinarith
      · -- if `N > 1`, we have `ε = 1/2` and hence `ε < N`.
        have hNgt1 : (1 : ℝ) < N := lt_of_not_ge hNle1
        have hrewrite : ε = (1 : ℝ) / 2 := by
          have : min N 1 = 1 := min_eq_right (le_of_lt hNgt1)
          simp [hεdef, this]
        nlinarith
    -- Step 2.2: show non-injectivity via the points `0` and `-1/ε`.
    refine ⟨ε, hεpos, hεltN, ?_⟩
    have hx₁ : (fun x : ℝ => x + ε * x ^ 2) 0 = 0 := by ring
    have hx₂ : (fun x : ℝ => x + ε * x ^ 2) (-1 / ε) = 0 := by
      have hεne : (ε : ℝ) ≠ 0 := ne_of_gt hεpos
      calc
        (fun x : ℝ => x + ε * x ^ 2) (-1 / ε)
            = (-1 / ε) + ε * ((-1 / ε) ^ 2) := rfl
        _ = (-1 / ε) + ε * (1 / ε ^ 2) := by ring
        _ = (-1 / ε) + (1 / ε) := by field_simp [hεne]
        _ = 0 := by ring
    -- Step 2.3: conclude that injectivity fails.
    intro hInj
    have hEq : (fun x : ℝ => x + ε * x ^ 2) 0 =
        (fun x : ℝ => x + ε * x ^ 2) (-1 / ε) := by
      simp [hx₂]
    have hxneq : (0 : ℝ) ≠ -1 / ε := by
      have hεne : (ε : ℝ) ≠ 0 := ne_of_gt hεpos
      have hne : (-1 / ε : ℝ) ≠ 0 := div_ne_zero (by norm_num) hεne
      simpa [eq_comm] using hne
    exact hxneq (hInj hEq)

/-
## Why the Original Formalization is Not Faithful

The original formalization has two issues:

1. It only assumes `Continuous g` instead of `Differentiable ℝ g`. The informal statement
   says "with bounded derivative", which implicitly requires differentiability. With only
   continuity, `deriv g x` is junk (zero by convention), making `|deriv g x| ≤ M` trivial
   but meaningless. The counterexample `g(x) = x²` above shows continuity alone doesn't
   suffice for the conclusion.

2. The corrected version below (`Rudin_exercise_5_3_corrected`) fixes the differentiability
   issue but its conclusion `∃ N, ∀ ε > 0, ε < N → Injective (...)` does not require `N > 0`.
   Taking `N = 0` makes the implication vacuously true (no ε is both > 0 and < 0). This makes
   the statement trivially provable regardless of g, hence strictly weaker than the informal
   claim which asserts a genuine positive threshold.

## Correction

1. Require `Differentiable ℝ g` (already done in `_corrected`).
2. Strengthen the conclusion to `∃ N > 0, ∀ ε > 0, ε < N → Injective (...)` so that the
   threshold is genuinely positive.
-/
theorem Rudin_exercise_5_3_corrected
  {g : ℝ → ℝ} (hgDiff : Differentiable ℝ g)
  (hg' : ∃ M : ℝ, ∀ x : ℝ, |deriv g x| ≤ M) :
  ∃ N > 0, ∀ ε > 0, ε < N → Function.Injective (λ x : ℝ => x + ε * g x) := by
  classical
  -- Step 1: extract a uniform bound `M` on the derivative and note `M ≥ 0`.
  obtain ⟨M, hM⟩ := hg'
  have hM_nonneg : 0 ≤ M := by
    -- Since `|deriv g 0| ≤ M` and absolute values are non‑negative, `M` must be non‑negative.
    have h := hM 0
    have h_abs : 0 ≤ |deriv g 0| := abs_nonneg _
    exact le_trans h_abs h

  -- Step 2: turn the derivative bound into a global Lipschitz bound for `g`.
  have hLip : LipschitzWith ⟨M, hM_nonneg⟩ g := by
    -- Step 2.1: upgrade the real bound to the `ℝ≥0` bound required by the lemma.
    have hBound : ∀ x, ‖deriv g x‖₊ ≤ ⟨M, hM_nonneg⟩ := by
      intro x
      have hreal : ‖deriv g x‖ ≤ M := by
        -- For real numbers `‖·‖ = |·|`.
        simpa [Real.norm_eq_abs] using hM x
      exact_mod_cast hreal
    -- Step 2.2: apply the mean value inequality specialized to one variable.
    exact lipschitzWith_of_nnnorm_deriv_le hgDiff hBound

  -- Step 3: choose a concrete admissible size for `ε`.
  -- We take `N = 1 / (M + 1)` so that `ε < N` implies `ε * M < 1`.
  refine ⟨1 / (M + 1), div_pos one_pos (by linarith), ?_⟩
  intro ε hεpos hεlt
  -- Step 3.1: show the crucial inequality `ε * M < 1`.
  have hεM_lt_one : ε * M < 1 := by
    -- Because `ε < 1/(M+1)` we have `ε*(M+1) < 1`, and `ε*M ≤ ε*(M+1)`.
    have h1 : ε * (M + 1) < 1 := by
      -- since `0 < M+1`, we can multiply the inequality by `(M+1)`
      have hpos : 0 < M + 1 := by linarith
      have hmult : ε * (M + 1) < (1 / (M + 1)) * (M + 1) :=
        mul_lt_mul_of_pos_right hεlt hpos
      have hcancel : (M + 1)⁻¹ * (M + 1) = (1 : ℝ) := by
        have hposne : (M + 1) ≠ 0 := by linarith
        field_simp [hposne]
      simpa [one_div, hcancel] using hmult
    have h2 : ε * M ≤ ε * (M + 1) := by nlinarith
    exact lt_of_le_of_lt h2 h1

  -- Step 4: prove injectivity using the Lipschitz bound.
  intro x y hEq
  -- Step 4.1: rearrange the assumed equality.
  have hDiff : x - y = ε * (g y - g x) := by
    linarith
  -- Step 4.2: take absolute values to prepare for estimates.
  have hAbs : |x - y| = ε * |g y - g x| := by
    have h := congrArg abs hDiff
    have hε : |ε| = ε := abs_of_pos hεpos
    -- `abs (a*b) = |a|*|b|`
    simpa [hε, abs_mul] using h

  -- Step 4.3: bound `|g y - g x|` using Lipschitzness.
  have hLip' : |g y - g x| ≤ M * |y - x| := by
    have h := hLip.dist_le_mul y x
    -- `dist` on `ℝ` is `|·|`; coercion of `ℝ≥0` to `ℝ` is the real value.
    simpa [Real.dist_eq, mul_comm] using h

  -- Step 4.4: combine the two estimates.
  have hAbs_le : |x - y| ≤ ε * (M * |x - y|) := by
    calc
      |x - y| = ε * |g y - g x| := hAbs
      _ ≤ ε * (M * |y - x|) := by
            have : |g y - g x| ≤ M * |y - x| := hLip'
            nlinarith
      _ = ε * (M * |x - y|) := by
        -- `|y - x| = |x - y|`
        have : |y - x| = |x - y| := by simp [abs_sub_comm]
        nlinarith

  -- Step 4.5: deduce `x = y` from the inequality.
  by_cases hxy : x = y
  · exact hxy
  · have hxydist_pos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    -- Divide the inequality by `|x - y| > 0` to obtain `1 ≤ ε * M`, contradicting `ε*M < 1`.
    have hOne : 1 ≤ ε * M := by
      -- `|x - y| ≤ ε*M*|x - y|` with `|x-y|>0` implies `1 ≤ ε*M`.
      have := hAbs_le
      nlinarith
    have hContr : False := not_le_of_gt hεM_lt_one hOne
    exact (hContr.elim)
