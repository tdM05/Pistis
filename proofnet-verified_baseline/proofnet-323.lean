import Mathlib

open Filter Real Function
open scoped Topology



/-Informal Statement

Assume that $f \colon \mathbb{R} \rightarrow \mathbb{R}$ satisfies $|f(t)-f(x)| \leq|t-x|^{2}$ for all $t, x$. Prove that $f$ is constant.
-/

/-Informal Proof

We have $|f(t)-f(x)| \leq|t-x|^2, \forall t, x \in \mathbb{R}$. Fix $x \in \mathbb{R}$ and let $t \neq x$. Then
$$
\left|\frac{f(t)-f(x)}{t-x}\right| \leq|t-x| \text {, hence } \lim _{t \rightarrow x}\left|\frac{f(t)-f(x)}{t-x}\right|=0 \text {, }
$$
so $f$ is differentiable in $\mathbb{R}$ and $f^{\prime}=0$. This implies that $f$ is constant, as seen in class.
-/

theorem Pugh_exercise_3_1 {f : ℝ → ℝ}
  (hf : ∀ x y, |f x - f y| ≤ |x - y| ^ 2) :
  ∃ c, f = λ _x => c := by
  classical
  -- Step 1: Prove that any two values of `f` coincide, using the quadratic modulus bound.
  have h_equal : ∀ x y : ℝ, f x = f y := by
    intro x y
    -- Step 1.1: If the points coincide, the claim is trivial.
    by_cases hxy : x = y
    · -- Step 1.1.1: When `x = y`, the values are equal by reflexivity.
      subst hxy; rfl
    · -- Step 1.2: Assume `x ≠ y` and force the absolute difference to be zero.
      -- Step 1.2.1: For each natural `n`, we partition the segment `[x,y]` into `n.succ` equal pieces.
      have main_bound : ∀ n : ℕ, |f y - f x| ≤ |y - x| ^ 2 / (n.succ : ℝ) := by
        intro n
        -- Step 1.2.1.1: Define the step length `h` of the partition.
        set h : ℝ := (y - x) / (n.succ : ℝ) with hh
        -- Step 1.2.1.2: Bound the cumulative difference after `m` steps of size `h`.
        have diff_bound : ∀ m : ℕ, |f (x + (m : ℝ) * h) - f x| ≤ (m : ℝ) * h ^ 2 := by
          intro m
          -- Step 1.2.1.2.1: Induct on `m` (the number of steps).
          induction m with
          | zero =>
              -- Step 1.2.1.2.1.1: At `m = 0`, there is no movement; the difference is zero.
              simp
          | succ m ih =>
              -- Step 1.2.1.2.1.2: Add one more step of length `h`.
              have h_step : |f (x + (m.succ : ℝ) * h) - f (x + (m : ℝ) * h)| ≤ h ^ 2 := by
                -- Step 1.2.1.2.1.2.1: Apply the given quadratic bound to two consecutive partition points.
                have hraw := hf (x + (m.succ : ℝ) * h) (x + (m : ℝ) * h)
                -- Step 1.2.1.2.1.2.1.1: Name the increment `u` between consecutive partition points.
                let u : ℝ := (x + (m.succ : ℝ) * h) - (x + (m : ℝ) * h)
                have hsq : |u| ^ 2 = u ^ 2 := by
                  -- squaring removes the absolute value for real numbers
                  have := sq_abs u
                  simp [pow_two]
                -- Step 1.2.1.2.1.2.1.2: Rewrite the bound using `u` and its square.
                have hraw' : |f (x + (m.succ : ℝ) * h) - f (x + (m : ℝ) * h)| ≤ u ^ 2 := by
                  simpa [u, hsq] using hraw
                -- Step 1.2.1.2.1.2.1.3: Replace `u` by the actual step size `h`.
                have hu : u = h := by
                  -- the spatial increment is exactly one copy of `h`
                  unfold u
                  have diff1 : (m.succ : ℝ) - (m : ℝ) = 1 := by
                    -- cast `m.succ` to ℝ and subtract to get the unit increment
                    have hm1 : (m.succ : ℝ) = (m : ℝ) + 1 := by norm_cast
                    linarith
                  calc
                    (x + (m.succ : ℝ) * h) - (x + (m : ℝ) * h)
                        = ((m.succ : ℝ) - (m : ℝ)) * h := by ring_nf
                    _ = (1 : ℝ) * h := by simp
                    _ = h := by ring
                simpa [u, hu] using hraw'
              -- Step 1.2.1.2.1.2.2: Use the triangle inequality to accumulate bounds.
              have htri :
                  |(f (x + (m.succ : ℝ) * h) - f (x + (m : ℝ) * h)) + (f (x + (m : ℝ) * h) - f x)|
                    ≤ |f (x + (m.succ : ℝ) * h) - f (x + (m : ℝ) * h)| + |f (x + (m : ℝ) * h) - f x| := by
                -- Step 1.2.1.2.1.2.2.1: Triangle inequality expressed with norms, specialized to real numbers.
                have htriangle := norm_add_le (f (x + (m.succ : ℝ) * h) - f (x + (m : ℝ) * h))
                  (f (x + (m : ℝ) * h) - f x)
                -- convert norms to absolute values
                simpa [Real.norm_eq_abs] using htriangle
              calc
                |f (x + (m.succ : ℝ) * h) - f x|
                    = |(f (x + (m.succ : ℝ) * h) - f (x + (m : ℝ) * h)) + (f (x + (m : ℝ) * h) - f x)| := by
                        ring_nf
                _ ≤ |f (x + (m.succ : ℝ) * h) - f (x + (m : ℝ) * h)| + |f (x + (m : ℝ) * h) - f x| := htri
                _ ≤ h ^ 2 + (m : ℝ) * h ^ 2 := by
                        have := add_le_add h_step ih
                        -- Step 1.2.1.2.1.2.2.2: The previous line accumulates the two bounds.
                        simpa [add_comm] using this
                _ = (m.succ : ℝ) * h ^ 2 := by
                      -- factor out `h^2` and identify `m.succ` with `m+1`
                      have hm1 : (m.succ : ℝ) = (m : ℝ) + 1 := by norm_cast
                      calc
                        h ^ 2 + (m : ℝ) * h ^ 2 = ((m : ℝ) + 1) * h ^ 2 := by ring
                        _ = (m.succ : ℝ) * h ^ 2 := by simp [hm1]
        -- Step 1.2.1.3: Show that advancing `n.succ` steps of size `h` lands exactly at `y`.
        have hxyn : x + (n.succ : ℝ) * h = y := by
          -- Step 1.2.1.3.1: The denominator `(n.succ : ℝ)` is nonzero because `n.succ ≥ 1`.
          have hnnz : (n.succ : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
          -- Step 1.2.1.3.2: Direct algebra using the definition of `h`.
          calc
            x + (n.succ : ℝ) * h
                = x + (n.succ : ℝ) * ((y - x) / (n.succ : ℝ)) := by rfl
            _ = x + (y - x) := by field_simp [h, hnnz]
            _ = y := by ring
        have hxyn' : x + ((n : ℝ) + 1) * h = y := by
          -- rewrite the previous identity to the form with an explicit `+ 1`
          have hcast : (n.succ : ℝ) = (n : ℝ) + 1 := by norm_cast
          simpa [hcast] using hxyn
        -- Step 1.2.1.4: Specialize the cumulative bound to exactly `n.succ` steps.
        have h_apply := diff_bound n.succ
        -- Step 1.2.1.5: Combine with endpoint identity to bound the total jump.
        have h_total : |f y - f x| ≤ (n.succ : ℝ) * h ^ 2 := by
          have := h_apply
          -- Step 1.2.1.5.1: Replace the endpoint with `y` using `hxyn`.
          simpa [hxyn'] using this
        -- Step 1.2.1.6: Rewrite the right-hand side into the clean fraction form.
        have h_norm : (n.succ : ℝ) * h ^ 2 = |y - x| ^ 2 / (n.succ : ℝ) := by
          -- Step 1.2.1.6.1: The casted natural number is positive.
          have hnnz : (n.succ : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
          -- Step 1.2.1.6.2: Expand `h` and simplify purely algebraically (no absolute values needed after squaring).
          calc
            (n.succ : ℝ) * h ^ 2
                = (n.succ : ℝ) * ((y - x) / (n.succ : ℝ)) ^ 2 := by simp [h]
            _ = (n.succ : ℝ) * ((y - x) ^ 2 / (n.succ : ℝ) ^ 2) := by ring
            _ = (y - x) ^ 2 / (n.succ : ℝ) := by
              -- cancel one factor of `(n.succ : ℝ)` from numerator and denominator
              have hpow : (n.succ : ℝ) ^ 2 ≠ 0 := by exact pow_ne_zero _ hnnz
              field_simp [hpow]
            _ = |y - x| ^ 2 / (n.succ : ℝ) := by
              -- Step 1.2.1.6.2.1: Square removes the sign, so we may replace `(y - x) ^ 2` with `|y - x| ^ 2`.
              have hsquare : |y - x| ^ 2 = (y - x) ^ 2 := by
                simp [pow_two]
              have hsymm := hsquare.symm
              -- apply the equality to both sides of the fraction
              have : (y - x) ^ 2 / (n.succ : ℝ) = |y - x| ^ 2 / (n.succ : ℝ) := by
                exact congrArg (fun t => t / (n.succ : ℝ)) hsymm
              simp
        -- Step 1.2.1.7: Combine the rewrites to obtain the desired partition bound.
        calc
          |f y - f x| ≤ (n.succ : ℝ) * h ^ 2 := h_total
          _ = |y - x| ^ 2 / (n.succ : ℝ) := h_norm
      -- Step 1.2.2: If `f x ≠ f y`, derive a contradiction using the bounds for large `n`.
      have h_nonneg : 0 ≤ |f y - f x| := abs_nonneg _
      by_contra hneq
      -- Step 1.2.2.1: From `f x ≠ f y`, the absolute difference is strictly positive.
      have hpos' : 0 < |f y - f x| := abs_pos.mpr (sub_ne_zero.mpr (ne_comm.mp hneq))
      -- Step 1.2.2.2: Choose a large `n` so that the denominator dominates the fixed numerator.
      obtain ⟨n, hn⟩ : ∃ n : ℕ, |y - x| ^ 2 / |f y - f x| < n := exists_nat_gt (|y - x| ^ 2 / |f y - f x|)
      -- Step 1.2.2.3: Strengthen the previous inequality to use `n.succ`.
      have hn' : |y - x| ^ 2 / |f y - f x| < (n.succ : ℝ) :=
        lt_trans hn (by exact_mod_cast Nat.lt_succ_self n)
      -- Step 1.2.2.4: Multiply by the positive number `|f y - f x|` to move it to the other side.
      have hmul : (y - x) ^ 2 < (n.succ : ℝ) * |f y - f x| := by
        have hmult := mul_lt_mul_of_pos_right hn' hpos'
        -- Step 1.2.2.4.1: Simplify the left-hand side after multiplication.
        have hne : |f y - f x| ≠ 0 := by exact ne_of_gt hpos'
        have hcancel₁ : (|y - x| ^ 2 / |f y - f x|) * |f y - f x| = |y - x| ^ 2 := by
          field_simp [hne]
        have hcancel₂ : (y - x) ^ 2 / |f y - f x| * |f y - f x| = (y - x) ^ 2 := by
          field_simp [hne]
        have hsquare : |y - x| ^ 2 = (y - x) ^ 2 := by simp [pow_two]
        -- rewrite `hmult` to a form with `(y - x)^2` explicitly
        have hineq : (y - x) ^ 2 / |f y - f x| * |f y - f x| < (n.succ : ℝ) * |f y - f x| := by
          have hineq' : (|y - x| ^ 2 / |f y - f x|) * |f y - f x| < (n.succ : ℝ) * |f y - f x| := hmult
          simpa [hsquare] using hineq'
        -- conclude by cancelling the denominator
        have hmult' : (y - x) ^ 2 < (n.succ : ℝ) * |f y - f x| := by
          simpa [hcancel₂] using hineq
        exact hmult'
      -- Step 1.2.2.5: Use the previously proved bound to get the reverse inequality.
      have hbound := main_bound n
      have hbound' : (n.succ : ℝ) * |f y - f x| ≤ |y - x| ^ 2 := by
        have hpossucc : 0 ≤ (n.succ : ℝ) := by exact_mod_cast Nat.zero_le (n.succ)
        -- multiply the bound by the nonnegative factor `(n.succ : ℝ)`
        have htmp : (n.succ : ℝ) * |f y - f x| ≤ (n.succ : ℝ) * (|y - x| ^ 2 / (n.succ : ℝ)) :=
          mul_le_mul_of_nonneg_left hbound hpossucc
        have hnnz : (n.succ : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        have hcancel : (n.succ : ℝ) * (|y - x| ^ 2 / (n.succ : ℝ)) = |y - x| ^ 2 := by
          field_simp [hnnz]
        linarith [htmp, hcancel]
      -- Step 1.2.2.6: The two inequalities contradict each other, so the assumption was impossible.
      have hcontr : (y - x) ^ 2 < (y - x) ^ 2 := by
        have hsquare_abs : |y - x| ^ 2 = (y - x) ^ 2 := by simp [pow_two]
        have hbound'' : (n.succ : ℝ) * |f y - f x| ≤ (y - x) ^ 2 := by
          simpa [hsquare_abs] using hbound'
        exact lt_of_lt_of_le hmul hbound''
      exact (lt_irrefl _ hcontr).elim
  -- Step 2: Having pairwise equality, define the constant value as `f 0`.
  refine ⟨f 0, ?_⟩
  -- Step 2.1: Use function extensionality to identify `f` with the constant function.
  funext x
  -- Step 2.2: Apply the pairwise equality with reference point `0`.
  exact h_equal x 0
