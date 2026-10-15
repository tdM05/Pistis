import Mathlib

open scoped BigOperators

/-!

## Formalization notes (VERY detailed)

We prove the statement by contradiction-free algebra using the classical
**tangent half-angle parametrization** of the unit circle.

### Big picture

The informal statement is:

> If `z₁,z₂,z₃,z₄ ∈ ℂ` satisfy `|zⱼ| = 1` and `zⱼ ≠ 1`, then
> `3 - z₁ - z₂ - z₃ - z₄ + z₁ z₂ z₃ z₄ ≠ 0`.

### Proof plan

Step 1. (Parametrize each `zⱼ` by a real number.)

For any `z : ℂ` with `‖z‖ = 1` and `z ≠ 1`, define

`t := (-I) * (z + 1) / (z - 1)`.

We show `t` is **real** (i.e. fixed by conjugation), hence `t = (t.re : ℂ)`.

Then we prove the explicit inversion identity

`(t - I) / (t + I) = z`.

So each `zⱼ` can be written as `(rⱼ - I) / (rⱼ + I)` for some `rⱼ : ℝ`.

Step 2. (Compute the target expression in terms of the real parameters.)

For `zⱼ = (rⱼ - I)/(rⱼ + I)` we compute

`3 - z₁ - z₂ - z₃ - z₄ + z₁ z₂ z₃ z₄`

as an explicit rational expression with denominator
`(r₁+I)(r₂+I)(r₃+I)(r₄+I)` and numerator
`(Σ_{i<j} rᵢ rⱼ - 2) + (r₁+r₂+r₃+r₄) * I`.

Step 3. (Show the numerator cannot be zero over ℝ.)

If that numerator were zero, taking real and imaginary parts would give

`r₁+r₂+r₃+r₄ = 0` and `Σ_{i<j} rᵢ rⱼ = 2`.

But then

`(r₁+r₂+r₃+r₄)^2 = r₁^2+r₂^2+r₃^2+r₄^2 + 2*Σ_{i<j} rᵢ rⱼ`

would imply `0 = (sum of squares) + 4`, impossible.

Therefore the original expression is nonzero.

-/

-- We will use a slightly higher heartbeat limit because we do a few `ring_nf` / `field_simp` steps.
set_option maxHeartbeats 1000000

/-Informal Statement

For $j \in\{1,2,3,4\}$, let $z_{j}$ be a complex number with $\left|z_{j}\right|=1$ and $z_{j} \neq 1$. Prove that $3-z_{1}-z_{2}-z_{3}-z_{4}+z_{1} z_{2} z_{3} z_{4} \neq 0 .$
-/

/-Informal Proof

It will suffice to show that for any $z_1, z_2, z_3, z_4 \in \mathbb{C}$ of modulus 1 such that $|3-z_1-z_2-z_3-z_4| = |z_1z_2z_3z_4|$, at least one of $z_1, z_2, z_3$ is equal to 1.

To this end, let $z_1=e^{\alpha i}, z_2=e^{\beta i}, z_3=e^{\gamma i}$ and 
\[
f(\alpha, \beta, \gamma)=|3-z_1-z_2-z_3|^2-|1-z_1z_2z_3|^2.
\]
 A routine calculation shows that 
\begin{align*}
f(\alpha, \beta, \gamma)&=
10 - 6\cos(\alpha) - 6\cos(\beta) - 6\cos(\gamma) \\
&\quad + 2\cos(\alpha + \beta + \gamma) + 2\cos(\alpha - \beta) \\
&\quad + 2\cos(\beta - \gamma) + 2\cos(\gamma - \alpha).
\end{align*}
Since the function $f$ is continuously differentiable, and periodic in each variable, $f$ has a maximum and a minimum and it attains these values only at points where $\nabla f=(0,0,0)$.  A routine calculation now shows that 
\begin{align*}
\frac{\partial f}{\partial \alpha} + \frac{\partial f}{\partial \beta} + \frac{\partial f}{\partial \gamma} &=
6(\sin(\alpha) +\sin(\beta)+\sin(\gamma)-  \sin(\alpha + \beta + \gamma)) \\
&=
24\sin\left(\frac{\alpha+\beta}{2}\right) \sin\left(\frac{\beta+\gamma}{2}\right)
\sin\left(\frac{\gamma+\alpha}{2}\right).
\end{align*}
Hence every critical point of $f$ must satisfy one of $z_1z_2=1$, $z_2z_3=1$, or $z_3z_1=1$. By symmetry, let us assume that $z_1z_2=1$. Then 
\[
f = |3-2\mathrm{Re}(z_1)-z_3|^2-|1-z_3|^2;
\]
since $3-2\mathrm{Re}(z_1)\ge 1$, $f$ is nonnegative and can be zero only if the real part of $z_1$, and hence also $z_1$ itself, is equal to $1$.
-/

/-!

## Helper Lemmas (all step-by-step)

We build the machinery described in the plan above.

-/

-- Step 0: a tiny (but crucial) helper about the denominator `(r + I)`.
-- Step 0.1: For `r : ℝ`, the complex number `r + I` has imaginary part `1`, hence is not `0`.
lemma real_add_I_ne_zero (r : ℝ) : ((r : ℂ) + Complex.I) ≠ 0 := by
  -- Step 0.2: Assume for contradiction that `r + I = 0`.
  intro h
  -- Step 0.3: Take imaginary parts of the equality `r + I = 0`.
  have him : (((r : ℂ) + Complex.I)).im = 0 := by
    -- The imaginary part of `0` is `0`, and rewriting by `h` gives the claim.
    simp [h]
  -- Step 0.4: But the imaginary part of `(r : ℂ) + I` is `1`, contradiction.
  -- `simp` computes this imaginary part automatically.
  simp at him

-- Step 1: Explicit computation of the target expression after the substitution
-- `zj = (rj - I) / (rj + I)`.
lemma expr_in_terms_of_r (r0 r1 r2 r3 : ℝ) :
    let z0 : ℂ := (r0 - Complex.I) / (r0 + Complex.I)
    let z1 : ℂ := (r1 - Complex.I) / (r1 + Complex.I)
    let z2 : ℂ := (r2 - Complex.I) / (r2 + Complex.I)
    let z3 : ℂ := (r3 - Complex.I) / (r3 + Complex.I)
    3 - z0 - z1 - z2 - z3 + z0 * z1 * z2 * z3 =
      (-4) *
          ((r0 * r1 + r0 * r2 + r0 * r3 + r1 * r2 + r1 * r3 + r2 * r3 - 2) +
            (r0 + r1 + r2 + r3) * Complex.I) /
        ((r0 + Complex.I) * (r1 + Complex.I) * (r2 + Complex.I) * (r3 + Complex.I)) := by
  -- Step 1.1: Unfold the `let`-bindings so that the goal is a plain identity.
  simp
  -- Step 1.2: Record that each denominator `(ri + I)` is nonzero.
  have h0 : (r0 : ℂ) + Complex.I ≠ 0 := real_add_I_ne_zero r0
  have h1 : (r1 : ℂ) + Complex.I ≠ 0 := real_add_I_ne_zero r1
  have h2 : (r2 : ℂ) + Complex.I ≠ 0 := real_add_I_ne_zero r2
  have h3 : (r3 : ℂ) + Complex.I ≠ 0 := real_add_I_ne_zero r3
  -- Step 1.3: Clear all denominators using `field_simp`.
  field_simp [h0, h1, h2, h3]
  -- Step 1.4: Expand and normalize the resulting polynomial identity.
  ring_nf
  -- Step 1.5: Simplify the powers of `I` that appear after expansion.
  simp (config := { failIfUnchanged := false }) [Complex.I_sq, Complex.I_pow_four]
  -- Step 1.6: Normalize one more time to close the goal.
  ring_nf

-- Step 2: The key non-vanishing lemma for the parametrized version.
lemma expr_ne_zero_of_r (r0 r1 r2 r3 : ℝ) :
    let z0 : ℂ := (r0 - Complex.I) / (r0 + Complex.I)
    let z1 : ℂ := (r1 - Complex.I) / (r1 + Complex.I)
    let z2 : ℂ := (r2 - Complex.I) / (r2 + Complex.I)
    let z3 : ℂ := (r3 - Complex.I) / (r3 + Complex.I)
    3 - z0 - z1 - z2 - z3 + z0 * z1 * z2 * z3 ≠ 0 := by
  -- Step 2.1: Unfold the `let`-bindings.
  simp
  -- Step 2.2: Assume for contradiction that the expression is `0`.
  intro h
  -- Step 2.3: Replace the expression using the explicit formula from `expr_in_terms_of_r`.
  have hform := expr_in_terms_of_r r0 r1 r2 r3
  have h' :
      (-4) *
            ((r0 * r1 + r0 * r2 + r0 * r3 + r1 * r2 + r1 * r3 + r2 * r3 - 2) +
              (r0 + r1 + r2 + r3) * Complex.I) /
          ((r0 + Complex.I) * (r1 + Complex.I) * (r2 + Complex.I) * (r3 + Complex.I)) =
        0 := by
    -- Step 2.3.1: `hform` is exactly the equality we need to rewrite the LHS of `h`.
    simpa [hform] using h

  -- Step 2.4: The denominator is nonzero, so `a / d = 0` implies `a = 0`.
  have hden0 :
      ((r0 + Complex.I) * (r1 + Complex.I) * (r2 + Complex.I) * (r3 + Complex.I) : ℂ) ≠ 0 := by
    -- Step 2.4.1: Each factor is nonzero; use `mul_ne_zero` repeatedly.
    have h0 : (r0 : ℂ) + Complex.I ≠ 0 := real_add_I_ne_zero r0
    have h1 : (r1 : ℂ) + Complex.I ≠ 0 := real_add_I_ne_zero r1
    have h2 : (r2 : ℂ) + Complex.I ≠ 0 := real_add_I_ne_zero r2
    have h3 : (r3 : ℂ) + Complex.I ≠ 0 := real_add_I_ne_zero r3
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3

  have hnum0 :
      (-4 : ℂ) *
            ((r0 * r1 + r0 * r2 + r0 * r3 + r1 * r2 + r1 * r3 + r2 * r3 - 2) +
              (r0 + r1 + r2 + r3) * Complex.I) =
        0 := by
    -- Step 2.4.2: Use `div_eq_zero_iff`.
    have hdiv := (div_eq_zero_iff).1 h'
    cases hdiv with
    | inl ha =>
        exact ha
    | inr hd =>
        exact (hden0 hd).elim

  -- Step 2.5: Cancel the nonzero scalar `(-4 : ℂ)`.
  have hcore0 :
      ((r0 * r1 + r0 * r2 + r0 * r3 + r1 * r2 + r1 * r3 + r2 * r3 - 2) +
        (r0 + r1 + r2 + r3) * Complex.I) =
        0 := by
    -- Step 2.5.1: `(-4 : ℂ) ≠ 0`.
    have h4 : (-4 : ℂ) ≠ 0 := by norm_num
    -- Step 2.5.2: From `a*b = 0`, conclude `b = 0`.
    exact (mul_eq_zero.mp hnum0).resolve_left h4

  -- Step 2.6: Extract imaginary part = 0 ⇒ `r0 + r1 + r2 + r3 = 0`.
  have hsum0 : r0 + r1 + r2 + r3 = 0 := by
    -- Step 2.6.1: Take imaginary parts of `hcore0`.
    have him :
        (((r0 * r1 + r0 * r2 + r0 * r3 + r1 * r2 + r1 * r3 + r2 * r3 - 2) +
            (r0 + r1 + r2 + r3) * Complex.I) : ℂ).im =
          0 := by
      simp [hcore0]
    -- Step 2.6.2: Simplify the imaginary part.
    simpa using him

  -- Step 2.7: Extract real part = 0 ⇒ `r0*r1 + ... + r2*r3 = 2`.
  have hpairs : r0 * r1 + r0 * r2 + r0 * r3 + r1 * r2 + r1 * r3 + r2 * r3 = 2 := by
    -- Step 2.7.1: Take real parts of `hcore0`.
    have hre :
        (((r0 * r1 + r0 * r2 + r0 * r3 + r1 * r2 + r1 * r3 + r2 * r3 - 2) +
            (r0 + r1 + r2 + r3) * Complex.I) : ℂ).re =
          0 := by
      simp [hcore0]
    -- Step 2.7.2: This simplifies to the real equation `(pairwiseSum - 2) = 0`.
    have hre' : (r0 * r1 + r0 * r2 + r0 * r3 + r1 * r2 + r1 * r3 + r2 * r3 - 2) = 0 := by
      simpa using hre
    -- Step 2.7.3: Rearrange.
    linarith

  -- Step 2.8: Use the identity `(sum)^2 = sumSquares + 2*sumPairs`.
  have hsq :
      (r0 + r1 + r2 + r3) ^ 2 =
        r0 ^ 2 + r1 ^ 2 + r2 ^ 2 + r3 ^ 2 +
          2 * (r0 * r1 + r0 * r2 + r0 * r3 + r1 * r2 + r1 * r3 + r2 * r3) := by
    ring

  -- Step 2.9: Substitute `hsum0` and `hpairs` into `hsq` to get `0 = (sumSquares) + 4`.
  have hcontr : (0 : ℝ) = r0 ^ 2 + r1 ^ 2 + r2 ^ 2 + r3 ^ 2 + 4 := by
    calc
      (0 : ℝ) = (r0 + r1 + r2 + r3) ^ 2 := by
        simp [hsum0]
      _ = r0 ^ 2 + r1 ^ 2 + r2 ^ 2 + r3 ^ 2 +
            2 * (r0 * r1 + r0 * r2 + r0 * r3 + r1 * r2 + r1 * r3 + r2 * r3) := hsq
      _ = r0 ^ 2 + r1 ^ 2 + r2 ^ 2 + r3 ^ 2 + 4 := by
        nlinarith [hpairs]

  -- Step 2.10: But the RHS is strictly positive (sum of squares ≥ 0, plus 4).
  have hpos : (0 : ℝ) < r0 ^ 2 + r1 ^ 2 + r2 ^ 2 + r3 ^ 2 + 4 := by
    have hnn : 0 ≤ r0 ^ 2 + r1 ^ 2 + r2 ^ 2 + r3 ^ 2 := by
      nlinarith
    linarith

  -- Step 2.11: Contradiction.
  exact (ne_of_lt hpos) hcontr

-- Step 3: Pure algebra: the inversion identity for the parametrization.
-- If `t := (-I) * (z + 1) / (z - 1)` then `(t - I)/(t + I) = z`.
lemma z_eq_t_form (z : ℂ) (hz1 : z ≠ 1) :
    (let t : ℂ := (-Complex.I) * (z + 1) / (z - 1)
     (t - Complex.I) / (t + Complex.I) = z) := by
  -- Step 3.1: Unfold the `let`.
  simp
  -- Step 3.2: Clear the denominator `z - 1`.
  have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  field_simp [hzsub]
  ring

-- Step 4: Show that the parameter `t` is real when `‖z‖ = 1`.
-- We do this by proving `conj(t) = t`, i.e. `(starRingEnd ℂ) t = t`.
lemma conj_t_eq_t (z : ℂ) (hz0 : ‖z‖ = 1) (hz1 : z ≠ 1) :
    let t : ℂ := (-Complex.I) * (z + 1) / (z - 1)
    (starRingEnd ℂ) t = t := by
  intro t
  -- Step 4.1: Introduce the conjugation ring endomorphism `c`.
  let c : ℂ →+* ℂ := starRingEnd ℂ

  -- Step 4.2: We will need `z ≠ 0` (follows from `‖z‖ = 1`).
  have hz0' : z ≠ 0 := by
    intro hz
    have : ‖z‖ = 0 := norm_eq_zero.2 hz
    simp [hz0] at this

  -- Step 4.3: Show the key fact `c z = z⁻¹`.
  have hcz : c z = z⁻¹ := by
    -- Step 4.3.1: Start from `RCLike.mul_conj`: `z * conj(z) = ‖z‖^2`.
    have h := (RCLike.mul_conj z)
    -- Step 4.3.2: Rewrite `‖z‖ = 1`.
    rw [hz0] at h
    -- Step 4.3.3: Simplify the RHS `((↑(1:ℝ):ℂ)^2)` to `1`.
    have hRHS : ((↑(1 : ℝ) : ℂ) ^ 2) = (1 : ℂ) := by simp
    have hmul : z * c z = (1 : ℂ) := h.trans hRHS
    -- Step 4.3.4: Multiply by `z⁻¹` on the left.
    have : z⁻¹ * (z * c z) = z⁻¹ * 1 := congrArg (fun w : ℂ => z⁻¹ * w) hmul
    -- Step 4.3.5: Simplify.
    simpa [mul_assoc, hz0'] using this

  -- Step 4.4: Compute `c t` by pushing `c` through the expression.
  dsimp [t]
  calc
    c ((-Complex.I) * (z + 1) / (z - 1))
        = c (-Complex.I) * c (z + 1) / c (z - 1) := by
            -- Step 4.4.1: Use `map_mul` and `map_div₀`.
            simp [map_div₀, map_mul]
    _ = (Complex.I) * (c z + 1) / (c z - 1) := by
          -- Step 4.4.2: Compute `c (-I) = I` and distribute `c` over `±`.
          have hcI : c (-Complex.I) = Complex.I := by
            -- Step 4.4.2.1: Use `Complex.conj_I : c(I) = -I`.
            have hI : c (Complex.I : ℂ) = -Complex.I := by
              simp [c]
            -- Step 4.4.2.2: Then `c(-I) = -c(I) = I`.
            calc
              c (-Complex.I : ℂ) = -c (Complex.I : ℂ) := by simp
              _ = -(-Complex.I) := by simp [hI]
              _ = Complex.I := by ring
          -- Step 4.4.2.3: Use `map_add`, `map_sub`.
          simp [hcI, map_add, map_sub]
    _ = Complex.I * (z⁻¹ + 1) / (z⁻¹ - 1) := by
          -- Step 4.4.3: Substitute `c z = z⁻¹`.
          simp [hcz]
    _ = (-Complex.I) * (z + 1) / (z - 1) := by
          -- Step 4.4.4: Pure algebraic simplification.
          -- We clear denominators; we need both `z ≠ 0` and `z ≠ 1`.
          have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
          have hzsub' : (1 - z) ≠ 0 := by
            intro h
            apply hzsub
            have : z - 1 = -(1 - z) := by ring
            simp [this, h]
          field_simp [hz0', hzsub, hzsub']
          ring

-- Step 5: Existence of a real parameter `r` with `z = (r - I)/(r + I)`.
lemma exists_real_param (z : ℂ) (hz0 : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ r : ℝ, z = (r - Complex.I) / (r + Complex.I) := by
  -- Step 5.1: Define the complex parameter `t`.
  let t : ℂ := (-Complex.I) * (z + 1) / (z - 1)

  -- Step 5.2: Show `conj(t) = t`, i.e. `(starRingEnd ℂ) t = t`.
  have ht_conj : (starRingEnd ℂ) t = t := by
    simpa [t] using (conj_t_eq_t z hz0 hz1)

  -- Step 5.3: Convert `conj(t) = t` into `t.im = 0`.
  have ht_im : t.im = 0 := (Complex.conj_eq_iff_im).1 ht_conj

  -- Step 5.4: Let `r := t.re`.
  refine ⟨t.re, ?_⟩

  -- Step 5.5: Show `t = (t.re : ℂ)`.
  have ht_eq : t = (t.re : ℂ) := by
    -- Step 5.5.1: Use `t = t.re + t.im * I`.
    have hdecomp : (t.re : ℂ) + (t.im : ℂ) * Complex.I = t := by
      -- `Complex.re_add_im` already states this.
      simp [Complex.re_add_im t]
    -- Step 5.5.2: Since `t.im = 0`, this simplifies to `t = t.re`.
    simpa [ht_im] using hdecomp.symm

  -- Step 5.6: Use the inversion identity `(t - I)/(t + I) = z`.
  have hz_t : (t - Complex.I) / (t + Complex.I) = z := by
    simpa [t] using (z_eq_t_form z hz1)

  -- Step 5.7: Substitute `t = (t.re : ℂ)`.
  have hz_t' := hz_t
  rw [ht_eq] at hz_t'

  -- Step 5.8: Conclude by symmetry.
  simpa using hz_t'.symm

theorem Putnam_exercise_2020_b5 (z : Fin 4 → ℂ) (hz0 : ∀ n, ‖z n‖ = 1)
  (hz1 : ∀ n, z n ≠ 1) :
  3 - z 0 - z 1 - z 2 - z 3 + (z 0) * (z 1) * (z 2) * (z 3) ≠ 0 := by
  -- Step 6: Reduce to the parametrized real form.
  --
  -- Step 6.1: For each `z n`, pick a real parameter `r n` such that
  -- `z n = (r n - I)/(r n + I)`.
  have ⟨r0, hr0⟩ := exists_real_param (z 0) (hz0 0) (hz1 0)
  have ⟨r1, hr1⟩ := exists_real_param (z 1) (hz0 1) (hz1 1)
  have ⟨r2, hr2⟩ := exists_real_param (z 2) (hz0 2) (hz1 2)
  have ⟨r3, hr3⟩ := exists_real_param (z 3) (hz0 3) (hz1 3)

  -- Step 6.2: Apply the already-proved non-vanishing lemma in the parametrized setting.
  have hne :
      3 - ((r0 - Complex.I) / (r0 + Complex.I)) - ((r1 - Complex.I) / (r1 + Complex.I)) -
            ((r2 - Complex.I) / (r2 + Complex.I)) - ((r3 - Complex.I) / (r3 + Complex.I)) +
          ((r0 - Complex.I) / (r0 + Complex.I)) * ((r1 - Complex.I) / (r1 + Complex.I)) *
              ((r2 - Complex.I) / (r2 + Complex.I)) * ((r3 - Complex.I) / (r3 + Complex.I)) ≠
        0 := by
    -- This is exactly `expr_ne_zero_of_r` after unfolding its `let`s.
    simpa using (expr_ne_zero_of_r r0 r1 r2 r3)

  -- Step 6.3: Rewrite back from the parametrized `rᵢ` to the original `z i`.
  simpa [hr0, hr1, hr2, hr3] using hne
