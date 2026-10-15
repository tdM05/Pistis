import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Let $f$ be defined for all real $x$, and suppose that $|f(x)-f(y)| \leq (x-y)^{2}$ for all real $x$ and $y$. Prove that $f$ is constant.
-/

/-Informal Proof

Dividing by $x-y$, and letting $x \rightarrow y$, we find that $f^{\prime}(y)=0$ for all $y$. Hence $f$ is constant.
-/

theorem Rudin_exercise_5_1
  {f : ℝ → ℝ} (hf : ∀ x y : ℝ, |(f x - f y)| ≤ (x - y) ^ 2) :
  ∃ c, f = λ _x => c := by
  classical
  /- Step 1: Establish a **uniform refined bound** using partitions.
     For any points `x` and `y` and any positive integer `n`,
     we show `|f x - f y| ≤ (x - y)^2 / n`.  We prove this by
     subdividing the interval from `y` to `x` into `n` equal pieces,
     bounding each increment via the hypothesis, and summing. -/
  have h_partition :
      ∀ x y : ℝ, ∀ n : ℕ, 0 < n → |f x - f y| ≤ (x - y)^2 / n := by
    -- Step 1.1: Fix arbitrary `x y : ℝ` and positive natural `n`.
    intro x y n hn_pos
    -- Step 1.2: Define the step length `s = (x - y) / n`.
    set s : ℝ := (x - y) / n with hs
    -- Step 1.3: Prove by induction that after `m` steps the accumulated
    --           difference is bounded by `m * s^2`.
    have h_step :
        ∀ m : ℕ, |f (y + m * s) - f y| ≤ (m : ℝ) * s ^ 2 := by
      intro m
      -- Step 1.3.1: Induct on `m`.
      induction m with
      | zero =>
          -- Base case `m = 0`: the difference is zero, the bound is zero.
          -- |f (y + 0*s) - f y| = |f y - f y| = 0 ≤ 0.
          simp
      | succ m ih =>
          -- Inductive step: assume the claim for `m`; prove for `m+1`.
          -- Step 1.3.1.1: Difference between successive partition points is exactly `s`.
          have h_delta :
              ((m.succ : ℝ) * s - (m : ℝ) * s) = s := by
            -- The jump between two adjacent mesh points equals exactly one `s`.
            have hm' : (m.succ : ℝ) - (m : ℝ) = 1 := by
              have hm'' : (m.succ : ℝ) = (m : ℝ) + 1 := by norm_cast
              linarith
            calc
              ((m.succ : ℝ) * s - (m : ℝ) * s)
                  = ((m.succ : ℝ) - (m : ℝ)) * s := by ring
              _ = (1 : ℝ) * s := by simp
              _ = s := by ring
          -- Step 1.3.1.2: Hypothesis `hf` applied to the two consecutive points
          --               yields a bound `≤ s^2` for this increment.
          have h_diff :
              (y + (m.succ) * s) - (y + m * s)
                = ((m.succ : ℝ) * s - (m : ℝ) * s) := by ring
          have h_raw' :
              |f (y + (m.succ) * s) - f (y + m * s)| ≤
                ((m.succ : ℝ) * s - (m : ℝ) * s) ^ 2 := by
            -- Apply the hypothesis, then rewrite the geometric difference.
            have hraw := hf (y + (m.succ) * s) (y + m * s)
            simpa [h_diff] using hraw
          have h_delta_sq :
              (((m : ℝ) + 1) * s - (m : ℝ) * s) ^ 2 = s ^ 2 := by
            have hm' : ((m : ℝ) + 1) - (m : ℝ) = 1 := by ring
            calc
              (((m : ℝ) + 1) * s - (m : ℝ) * s) ^ 2
                  = ((((m : ℝ) + 1) - (m : ℝ)) * s) ^ 2 := by ring
              _ = (1 * s) ^ 2 := by simp [hm']
              _ = s ^ 2 := by ring
          have h_increment :
              |f (y + (m.succ) * s) - f (y + m * s)| ≤ s ^ 2 := by
            simpa [h_delta_sq] using h_raw'
          -- Step 1.3.1.3: Triangle inequality to combine the new increment with the accumulated part.
          have h_triangle :
              |f (y + (m.succ) * s) - f y|
                ≤ |f (y + (m.succ) * s) - f (y + m * s)|
                  + |f (y + m * s) - f y| := by
            -- Use the standard inequality `|a + b| ≤ |a| + |b|`, rewriting the sum appropriately.
            have hrewrite :
                f (y + (m.succ) * s) - f y
                  = (f (y + (m.succ) * s) - f (y + m * s))
                      + (f (y + m * s) - f y) := by ring
            -- Apply the triangle inequality for absolute values.
            have h := abs_add_le (f (y + (m.succ) * s) - f (y + m * s))
                                 (f (y + m * s) - f y)
            -- Unpack the rewrite to fit the lemma.
            have h' : |(f (y + (m.succ) * s) - f (y + m * s))
                        + (f (y + m * s) - f y)|
                        ≤ |f (y + (m.succ) * s) - f (y + m * s)|
                          + |f (y + m * s) - f y| := by simpa using h
            simpa [hrewrite] using h'
          -- Step 1.3.1.4: Combine bounds using the inductive hypothesis.
          calc
            |f (y + (m.succ) * s) - f y|
                ≤ |f (y + (m.succ) * s) - f (y + m * s)| +
                    |f (y + m * s) - f y| := h_triangle
            _ ≤ s ^ 2 + |f (y + m * s) - f y| := by nlinarith
            _ ≤ s ^ 2 + (m : ℝ) * s ^ 2 := by nlinarith
            _ = (m.succ : ℝ) * s ^ 2 := by
              -- Convert `(m.succ : ℝ)` into `(m : ℝ) + 1` and rearrange.
              have hm : (m.succ : ℝ) = (m : ℝ) + 1 := by norm_cast
              nlinarith [hm]
    -- Step 1.4: Evaluate the inductive bound at `m = n` to compare `f x` and `f y`.
    have h_at_n : |f (y + n * s) - f y| ≤ (n : ℝ) * s ^ 2 := h_step n
    -- Step 1.5: Simplify `y + n * s` to `x` using the definition of `s` and `n ≠ 0`.
    have h_n_nonzero : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn_pos
    -- Compute `n * s = x - y`, hence `y + n * s = x`.
    have h_y_add : y + n * s = x := by
      -- Rewrite using `s = (x - y)/n`.
      have hmul : (n : ℝ) * s = x - y := by
        -- (n) * ((x - y)/n) = x - y when `n ≠ 0`.
        have h_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn_pos)
        -- Rewrite using the definition of `s`.
        have : (n : ℝ) * ((x - y) / n) = x - y := by
          field_simp [h_ne]
        simpa [hs] using this
      calc
        y + n * s = y + (x - y) := by simp [hmul]
        _ = x := by ring
    -- Step 1.6: Replace and simplify the bound.
    -- First, rewrite the left side with `h_y_add`.
    have h_abs_rewrite :
        |f (y + n * s) - f y| = |f x - f y| := by simp [h_y_add]
    -- Next, compute `(n : ℝ) * s^2` in terms of `(x - y)^2 / n`.
    have h_right_rewrite :
        (n : ℝ) * s ^ 2 = (x - y) ^ 2 / n := by
      -- Expand `s`, simplify the algebra, and use `n ≠ 0`.
      have hpos : (n : ℝ) ≠ 0 := h_n_nonzero
      -- Rewrite the square of a quotient and cancel one factor of `n`.
      calc
        (n : ℝ) * s ^ 2
            = (n : ℝ) * ((x - y) / n) ^ 2 := by simp [hs]
        _ = (n : ℝ) * ((x - y) ^ 2 / (n : ℝ) ^ 2) := by
                simp [div_pow]
        _ = (x - y) ^ 2 / n := by
                -- `(n)/(n^2) = 1/n`, so multiply and simplify.
                field_simp [pow_two, hpos]
    -- Step 1.7: Combine the rewrites to finish this sub‑lemma.
    calc
      |f x - f y| = |f (y + n * s) - f y| := by simp [h_abs_rewrite]
      _ ≤ (n : ℝ) * s ^ 2 := h_at_n
      _ = (x - y) ^ 2 / n := h_right_rewrite

  /- Step 2: Show **pointwise equality** `f x = f y` for all `x y`.
     We use the refined bound: for any `ε > 0` we can choose a large
     integer `n` so that `(x - y)^2 / n < ε`, forcing
     `|f x - f y| < ε`.  The only real number smaller than every
     positive `ε` in absolute value is `0`, so the difference vanishes. -/
  have h_eq : ∀ x y : ℝ, f x = f y := by
    intro x y
    -- Step 2.1: Show the difference has arbitrarily small absolute value.
    have h_eps : ∀ ε > 0, |f x - f y| < ε := by
      intro ε hε_pos
      -- Step 2.1.1: By Archimedean property, pick natural `n` with `(x - y)^2 / ε < n`.
      obtain ⟨n, hn_gt⟩ := exists_nat_gt ((x - y) ^ 2 / ε)
      -- Ensure `n` is positive (follows from the strict inequality).
      have hnonneg : (0 : ℝ) ≤ (x - y) ^ 2 / ε := by
        have hxynonneg : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
        exact div_nonneg hxynonneg (le_of_lt hε_pos)
      have hn_pos_real : (0 : ℝ) < n := by linarith
      have hn_pos : 0 < n := by exact_mod_cast hn_pos_real
      -- Step 2.1.2: Apply the partition bound with this `n`.
      have h_bound := h_partition x y n hn_pos
      -- Step 2.1.3: Convert `hn_gt : (x - y)^2 / ε < n` into
      --             `(x - y)^2 / n < ε` using positivity of `ε` and `n`.
      have h_mul : (x - y) ^ 2 < (n : ℝ) * ε := by
        -- Multiply both sides of `hn_gt` by positive `ε`.
        have h := (mul_lt_mul_iff_left₀ hε_pos).mpr hn_gt
        have h_simpl : (x - y) ^ 2 / ε * ε = (x - y) ^ 2 := by
          have hε_ne : ε ≠ 0 := by exact (ne_of_gt hε_pos)
          field_simp [hε_ne]
        simpa [h_simpl, mul_comm, mul_left_comm, mul_assoc] using h
      have h_lt_eps : (x - y) ^ 2 / n < ε := by
        -- Divide the inequality `(x - y)^2 < n * ε` by positive `n`.
        have hposn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
        have h_mul_comm : (x - y) ^ 2 < ε * (n : ℝ) := by simpa [mul_comm] using h_mul
        have h_div := (div_lt_iff₀ hposn_real).mpr h_mul_comm
        simpa using h_div
      -- Step 2.1.4: Combine the bounds to get the desired `< ε`.
      exact lt_of_le_of_lt h_bound h_lt_eps
    -- Step 2.2: Conclude `|f x - f y| = 0` because it is smaller than every `ε > 0`.
    have h_abs_zero : |f x - f y| = 0 := by
      -- If the absolute difference were positive, choose ε = half of it for a contradiction.
      by_contra hneq
      have hpos : |f x - f y| > 0 := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hneq)
      -- Take ε = |f x - f y| / 2 > 0.
      have hε_pos : 0 < |f x - f y| / 2 := by nlinarith
      have hcontr := h_eps (|f x - f y| / 2) hε_pos
      -- Contradiction: |f x - f y| < |f x - f y| / 2.
      linarith
    -- Step 2.3: Convert absolute value equality to pointwise equality.
    have h_sub_zero : f x - f y = 0 := abs_eq_zero.mp h_abs_zero
    -- Step 2.4: Rearrange to `f x = f y`.
    exact sub_eq_zero.mp h_sub_zero

  /- Step 3: Define the constant value `c = f 0` and use function
     extensionality together with `h_eq` to show that `f` equals this constant. -/
  refine ⟨f 0, ?_⟩
  -- Step 3.1: Use `funext` for pointwise equality.
  apply funext
  intro x
  -- Step 3.2: Apply the pointwise equality lemma with `y = 0`.
  have := h_eq x 0
  -- Step 3.3: Rewrite.
  simpa using this
