import Mathlib

open InnerProductSpace RCLike ContinuousLinearMap Complex
open scoped BigOperators



/-Informal Statement

Suppose $u, v \in V$. Prove that $\langle u, v\rangle=0$ if and only if $\|u\| \leq\|u+a v\|$ for all $a \in \mathbf{F}$.
-/

/-Informal Proof

First off, let us suppose that $(u, v)=0$.
Now, let $a \in \mathbb{F}$. Next, $u, a v$ are orthogonal.
The Pythagorean theorem thus implies that
$$
\begin{aligned}
\|u+a v\|^2 & =\|u\|^2+\|a v\|^2 \\
& \geq\|u\|^2
\end{aligned}
$$
So, by taking the square roots, this will now give us $\|u\| \leq\|u+a v\|$.
Now, to prove the implication in the other direction, we must now let $\|u\| \leq$ $\|u+a v\|$ for all $a \in \mathbb{F}$. Squaring this inequality, we get both:
$$
\begin{gathered}
\|u\|^2 a n d \leq\|u+a v\|^2 \\
=(u+a v, u+a v) \\
=(u, u)+(u, a v)+(a v, u)+(a v, a v) \\
=\|u\|^2+\bar{a}(u, v)+a \overline{(u, v)}+|a|^2\|v\|^2 \\
\|u\|^2+2 \Re \bar{a}(u, v)+|a|^2\|v\|^2
\end{gathered}
$$
for all $a \in \mathbb{F}$.
Therefore,
$$
-2 \Re \bar{a}(u, v) \leq|a|^2\|v\|^2
$$
for all $a \in \mathbb{F}$. In particular, we can let $a$ equal $-t(u, v)$ for $t>0$. Substituting this value for $a$ into the inequality above gives
$$
2 t|(u, v)|^2 \leq t^2|(u, v)|^2\|v\|^2
$$
for all $t>0$.
Step 4
4 of 4
Divide both sides of the inequality above by $t$, getting
$$
2|(u, v)|^2 \leq t \mid(u, v)^2\|v\|^2
$$
for all $t>0$. If $v=0$, then $(u, v)=0$, as desired. If $v \neq 0$, set $t$ equal to $1 /\|v\|^2$ in the inequality above, getting
$$
2|(u, v)|^2 \leq|(u, v)|^2,
$$
which implies that $(u, v)=0$.
-/

theorem Axler_exercise_6_2 {V : Type*} [NormedAddCommGroup V] [RCLike F]
    [InnerProductSpace F V] [NormedField F] [Module F V] (u v : V) :
    ⟪u, v⟫_F = 0 ↔ ∀ (a : F), ‖u‖ ≤ ‖u + a • v‖ := by
  sorry

/-
 `[RCLike F]` equips `F` with its canonical normed-field structure, and the
`[InnerProductSpace F V]` instance already includes the compatible `NormedSpace`
(and therefore `Module`) structure on `V`.  Re-stating `[NormedField F]` or
`[Module F V]` would duplicate instances, so we keep only these minimal assumptions.

The redundant [NormedField F] / [Module F V] hypotheses trigger a typeclass-coherence clash: the lemmas we rely on (e.g. inner_smul_right, norm_smul, the Pythagorean identities) are registered for the canonical scalar-field and module structures that the RCLike/InnerProductSpace instances already provide.

After reordering the hypotheses to put the canonical [RCLike F]/[InnerProductSpace F V] first, Lean still elaborates the goal using the explicitly provided [NormedField F]/[Module F V]. Those can disagree with the canonical structures that inner_smul_right, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero, etc. expect, so every attempt (whether copying the original proof, reusing the minimal lemma, or shadowing with haveI) hits the same elaboration mismatch you saw.

In practice the only robust fix is to drop the redundant typeclass parameters
-/

/-
Step-by-step explanation of why `Axler_exercise_6_2` is *false* in its universally-closed form:
Step 1: With the explicit `[Module F V]` binder in scope, the `•` in the goal resolves to
        that explicit instance, NOT to the InnerProductSpace-derived one.  So the universal
        statement quantifies over every Module action on `V`, not just the canonical one.
Step 2: Take `V = WithLp 2 (ℂ × ℂ)`, `F = ℂ`, the canonical NormedAddCommGroup /
        InnerProductSpace structures, but supply a NON-canonical `Module ℂ V` whose action
        is `a •' (z₁, z₂) := (a · z₁, conj(a) · z₂)` — i.e. the standard action on the first
        component and the conjugate action on the second.  This is a valid Module structure
        (all six axioms hold), and it is genuinely different from the canonical one.
Step 3: At `u = (1, 1)`, `v = (-i, i)`, the canonical inner product `⟪u, v⟫_ℂ` is
        `conj(1)·(-i) + conj(1)·i = 0`, so the LHS of the iff holds.
Step 4: At `a = -i`, the twisted action gives
        `(-i) •' (-i, i) = ((-i)·(-i), conj(-i)·i) = (i·i, i·i) = (-1, -1)`,
        so `u + (-i) •' v = (0, 0)` and `‖u + (-i) •' v‖ = 0 < √2 = ‖u‖`.  The RHS fails.
Step 5: LHS true, RHS false ⇒ the iff fails at this witness ⇒ the universally-closed
        original cannot hold.
-/
theorem Axler_exercise_6_2_neg :
    ¬ (∀ (V : Type) [_inst1 : NormedAddCommGroup V] (F : Type) [_inst2 : RCLike F]
        [_inst3 : InnerProductSpace F V] [_inst4 : NormedField F] [_inst5 : Module F V]
        (u v : V), ⟪u, v⟫_F = 0 ↔ ∀ (a : F), ‖u‖ ≤ ‖u + a • v‖) := by
  -- Step 1: Assume the universally-closed original; we will derive `False`.
  intro h
  -- Step 2: Construct the twisted SMul on `V := WithLp 2 (ℂ × ℂ)`:
  --         smul' a x := toLp 2 (a * (ofLp x).1, star a * (ofLp x).2).
  let smul' : ℂ → WithLp 2 (ℂ × ℂ) → WithLp 2 (ℂ × ℂ) :=
    fun a x => WithLp.toLp 2 ((a * (WithLp.ofLp x).1 : ℂ),
                              (star a * (WithLp.ofLp x).2 : ℂ))
  -- Step 2.1: Helper to reduce equality on `WithLp 2 (ℂ × ℂ)` to equality on `ℂ × ℂ`.
  have eqOf : ∀ (x y : WithLp 2 (ℂ × ℂ)),
      ((WithLp.ofLp x : ℂ × ℂ) = (WithLp.ofLp y : ℂ × ℂ)) → x = y := by
    intro x y hxy; exact WithLp.ofLp_injective 2 hxy
  -- Step 2.2: Verify the six Module axioms for the twisted smul.
  let twisted : Module ℂ (WithLp 2 (ℂ × ℂ)) :=
    { smul := smul'
      one_smul := fun x => by
        apply eqOf
        show (((1 : ℂ) * (WithLp.ofLp x).1 : ℂ),
              (star (1 : ℂ) * (WithLp.ofLp x).2 : ℂ)) = WithLp.ofLp x
        ext <;> simp
      mul_smul := fun a b x => by
        apply eqOf
        show (((a * b) * (WithLp.ofLp x).1 : ℂ),
              (star (a * b) * (WithLp.ofLp x).2 : ℂ)) =
              ((a * (b * (WithLp.ofLp x).1) : ℂ),
               (star a * (star b * (WithLp.ofLp x).2) : ℂ))
        ext
        · simp [mul_assoc]
        · rw [star_mul]; ring
      smul_zero := fun a => by
        apply eqOf
        show ((a * (WithLp.ofLp (0 : WithLp 2 (ℂ × ℂ))).1 : ℂ),
              (star a * (WithLp.ofLp (0 : WithLp 2 (ℂ × ℂ))).2 : ℂ))
              = WithLp.ofLp (0 : WithLp 2 (ℂ × ℂ))
        ext <;> simp
      smul_add := fun a x y => by
        apply eqOf
        show ((a * (WithLp.ofLp (x + y)).1 : ℂ),
              (star a * (WithLp.ofLp (x + y)).2 : ℂ)) =
              ((a * (WithLp.ofLp x).1 + a * (WithLp.ofLp y).1 : ℂ),
               (star a * (WithLp.ofLp x).2 + star a * (WithLp.ofLp y).2 : ℂ))
        ext
        · show a * ((WithLp.ofLp x).1 + (WithLp.ofLp y).1) =
                a * (WithLp.ofLp x).1 + a * (WithLp.ofLp y).1
          ring
        · show star a * ((WithLp.ofLp x).2 + (WithLp.ofLp y).2) =
                star a * (WithLp.ofLp x).2 + star a * (WithLp.ofLp y).2
          ring
      add_smul := fun a b x => by
        apply eqOf
        show (((a + b) * (WithLp.ofLp x).1 : ℂ),
              (star (a + b) * (WithLp.ofLp x).2 : ℂ)) =
              ((a * (WithLp.ofLp x).1 + b * (WithLp.ofLp x).1 : ℂ),
               (star a * (WithLp.ofLp x).2 + star b * (WithLp.ofLp x).2 : ℂ))
        ext
        · ring
        · simp [star_add, add_mul]
      zero_smul := fun x => by
        apply eqOf
        show (((0 : ℂ) * (WithLp.ofLp x).1 : ℂ),
              (star (0 : ℂ) * (WithLp.ofLp x).2 : ℂ))
              = WithLp.ofLp (0 : WithLp 2 (ℂ × ℂ))
        ext <;> simp }
  -- Step 3: Specialise the assumed universal statement at our witness.
  let u : WithLp 2 (ℂ × ℂ) := WithLp.toLp 2 ((1 : ℂ), (1 : ℂ))
  let v : WithLp 2 (ℂ × ℂ) := WithLp.toLp 2 ((-Complex.I, Complex.I))
  have hiff := @h (WithLp 2 (ℂ × ℂ)) _ ℂ _ _ _ twisted u v
  -- Step 4: The LHS of the iff is true: the canonical inner product vanishes.
  --         ⟪(1,1), (-i, i)⟫ = conj(1)·(-i) + conj(1)·i = 0.
  have hLHS : (⟪u, v⟫_ℂ : ℂ) = 0 := by
    show (⟪WithLp.toLp 2 ((1 : ℂ), (1 : ℂ)),
          WithLp.toLp 2 ((-Complex.I, Complex.I) : ℂ × ℂ)⟫_ℂ : ℂ) = 0
    simp [WithLp.prod_inner_apply, RCLike.inner_apply]
  -- Step 5: Forward direction yields the universally-quantified RHS, but its `•`
  --         is the TWISTED action because we passed `twisted` to fill `[Module F V]`.
  have hUniv := hiff.mp hLHS
  -- Step 5.1: Specialise the universal statement to `a = -i`.
  have hAI := hUniv (-Complex.I)
  -- Step 6: Compute the twisted action `(-i) •' v` explicitly and project to ℂ × ℂ.
  --         (-i) •' (-i, i) = ((-i)·(-i), star(-i)·i) = (i², i·i) = (-1, -1).
  have h_smul_pair :
      (WithLp.ofLp ((twisted.toDistribMulAction.toMulAction.toSMul.smul (-Complex.I) v))
        : ℂ × ℂ) = ((-1 : ℂ), (-1 : ℂ)) := by
    show ((-Complex.I) * (WithLp.ofLp v).1, star (-Complex.I) * (WithLp.ofLp v).2)
          = ((-1 : ℂ), (-1 : ℂ))
    show ((-Complex.I) * (-Complex.I), star (-Complex.I) * Complex.I)
          = ((-1 : ℂ), (-1 : ℂ))
    ext
    · -- (-i)·(-i) = i² = -1
      show (-Complex.I) * (-Complex.I) = (-1 : ℂ)
      rw [neg_mul_neg]; exact Complex.I_mul_I
    · -- star(-i)·i = i·i = -1
      show star (-Complex.I) * Complex.I = (-1 : ℂ)
      simp [Complex.I_mul_I]
  -- Step 6.1: Lift the projected equality back to a `WithLp 2` equality.
  have h_smul_v :
      twisted.toDistribMulAction.toMulAction.toSMul.smul (-Complex.I) v
        = WithLp.toLp 2 ((-1 : ℂ), (-1 : ℂ)) := eqOf _ _ (by rw [h_smul_pair])
  -- Step 6.2: Compute u + (-i) •' v = (1, 1) + (-1, -1) = (0, 0).
  have h_sum :
      u + twisted.toDistribMulAction.toMulAction.toSMul.smul (-Complex.I) v
        = WithLp.toLp 2 ((0 : ℂ), (0 : ℂ)) := by
    rw [h_smul_v]
    apply eqOf
    show (WithLp.ofLp ((WithLp.toLp 2 ((1 : ℂ), (1 : ℂ)))
            + (WithLp.toLp 2 ((-1 : ℂ), (-1 : ℂ)))) : ℂ × ℂ) = ((0 : ℂ), (0 : ℂ))
    ext <;> simp
  -- Step 6.3: That sum has L²-norm 0.
  have h_norm_zero :
      ‖u + twisted.toDistribMulAction.toMulAction.toSMul.smul (-Complex.I) v‖ = 0 := by
    rw [h_sum]
    show ‖WithLp.toLp 2 ((0 : ℂ), (0 : ℂ))‖ = 0
    rw [WithLp.prod_norm_eq_of_L2]; simp
  -- Step 7: Compute ‖u‖ = √2 (the L² norm of (1, 1)).
  have h_u_norm : ‖u‖ = Real.sqrt 2 := by
    show ‖WithLp.toLp 2 ((1 : ℂ), (1 : ℂ))‖ = Real.sqrt 2
    rw [WithLp.prod_norm_eq_of_L2]
    simp
    norm_num
  -- Step 8: The display `(-i) • v` in `hAI` is defeq to twisted's smul applied; cast.
  have hAI' :
      ‖u‖ ≤ ‖u + twisted.toDistribMulAction.toMulAction.toSMul.smul (-Complex.I) v‖ := hAI
  -- Step 8.1: Substitute the computed norms to obtain `√2 ≤ 0`.
  rw [h_norm_zero, h_u_norm] at hAI'
  -- Step 8.2: But √2 > 0, contradiction.
  have h_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  linarith

theorem Axler_exercise_6_2_corrected {V : Type*} [NormedAddCommGroup V] {F : Type*}
    [RCLike F] [InnerProductSpace F V]
    (u v : V) :
    ⟪u, v⟫_F = 0 ↔ ∀ (a : F), ‖u‖ ≤ ‖u + a • v‖ := by
  classical
  constructor
  · -- Step 1: Assume the inner product between `u` and `v` is zero.
    intro hinner a
    -- Step 1.2: Show that `u` is orthogonal to `a • v` by sesquilinearity of the inner product.
    have h_ortho : ⟪u, a • v⟫_F = 0 := by
      -- Step 1.2.1: Rewrite the inner product using linearity in the second component.
      calc
        ⟪u, a • v⟫_F = a * ⟪u, v⟫_F := inner_smul_right (𝕜 := F) u v a
        _ = a * 0 := by simp [hinner]
        _ = 0 := by simp
    -- Step 1.3: Apply the Pythagorean identity to `u` and `a • v`.
    have h_pyth : ‖u + a • v‖ ^ 2 = ‖u‖ ^ 2 + ‖a • v‖ ^ 2 := by
      -- Step 1.3.1: Convert the multiplicative form supplied by Mathlib to the additive form we want.
      have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u (a • v) (by simpa using h_ortho)
      simpa [pow_two] using this
    -- Step 1.4: Use the nonnegativity of squares to bound the right-hand side from below by `‖u‖ ^ 2`.
    have h_sq_le : ‖u‖ ^ 2 ≤ ‖u + a • v‖ ^ 2 := by
      -- Step 1.4.1: The term `‖a • v‖ ^ 2` is nonnegative, so adding it only increases `‖u‖ ^ 2`.
      have h_base : ‖u‖ ^ 2 ≤ ‖u‖ ^ 2 + ‖a • v‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
      -- Step 1.4.2: Replace the sum of squares with `‖u + a • v‖ ^ 2` via the Pythagorean identity.
      simp [h_pyth]
    -- Step 1.5: Translate the inequality on squares back to the statement about norms, using monotonicity of the square root.
    have h_sqrt := Real.sqrt_le_sqrt h_sq_le
    -- Step 1.5.1: Square roots of squared norms collapse back to norms because norms are nonnegative.
    simpa [Real.sqrt_sq, norm_nonneg] using h_sqrt
  · -- Step 2: Assume the norm inequality holds for every scalar and prove the inner product vanishes.
    intro h
    -- Step 2.1: Argue by contradiction and suppose the inner product is nonzero.
    by_contra hinner
    have hinner_ne : ⟪u, v⟫_F ≠ 0 := by simpa using hinner
    -- Step 2.2: Show that `v` itself cannot be zero, otherwise the inner product would vanish immediately.
    have hv : v ≠ 0 := by
      -- Step 2.2.1: If `v = 0`, the right argument of the inner product is zero, contradicting `hinner_ne`.
      intro hv_zero
      have : ⟪u, v⟫_F = 0 := by simp [hv_zero]
      exact hinner this
    -- Step 2.3: Record that the self-inner-product of `v` is nonzero, so the inverse that appears below makes sense.
    have hv_inner : ⟪v, v⟫_F ≠ 0 := (inner_self_ne_zero).2 hv
    -- Step 2.4: Pick the scalar that cancels the component of `u` in the `v`-direction after conjugation.
    set b : F := -⟪u, v⟫_F * (⟪v, v⟫_F)⁻¹ with hb
    set a : F := star b with ha
    -- Step 2.5: Verify that the auxiliary scalars are nonzero (needed to get a strict inequality later).
    have hb_ne : b ≠ 0 := by
      -- Step 2.5.1: Both the numerator and denominator are nonzero, so their product is nonzero as well.
      have hnum : -⟪u, v⟫_F ≠ 0 := neg_ne_zero.mpr hinner_ne
      have hden : (⟪v, v⟫_F)⁻¹ ≠ 0 := inv_ne_zero hv_inner
      simpa [hb] using mul_ne_zero hnum hden
    have ha_ne : a ≠ 0 := by
      -- Step 2.5.2: Conjugation preserves nonvanishing, so take the conjugate to reduce to `hb_ne`.
      intro ha_zero
      have : b = 0 := by
        have h_star_eq : star (star b) = (0 : F) := by
          simpa [ha, star_zero] using congrArg star ha_zero
        simpa [star_star] using h_star_eq
      exact hb_ne this
    -- Step 2.6: Show that `u + a • v` is orthogonal to `v` with this specific choice of `a`.
    have h_conj : star a = b := by simp [ha]
    have h_ortho_v : ⟪u + a • v, v⟫_F = 0 := by
      -- Step 2.6.1: Expand and substitute the chosen scalar to make the cross term disappear.
      calc
        ⟪u + a • v, v⟫_F
            = ⟪u, v⟫_F + ⟪a • v, v⟫_F := by simp [inner_add_left]
        _ = ⟪u, v⟫_F + star a * ⟪v, v⟫_F := by simp [inner_smul_left]
        _ = ⟪u, v⟫_F + b * ⟪v, v⟫_F := by simp [h_conj]
        _ = ⟪u, v⟫_F + (-⟪u, v⟫_F * (⟪v, v⟫_F)⁻¹) * ⟪v, v⟫_F := by simp [hb]
        _ = ⟪u, v⟫_F + (-⟪u, v⟫_F) := by
          -- Step 2.6.1.1: Cancel the invertible factor `⟪v, v⟫` with its inverse.
          congr 1
          rw [mul_assoc, inv_mul_cancel₀ hv_inner, mul_one]
        _ = 0 := by simp
    -- Step 2.7: Evaluate the inequality hypothesis at the special scalar `a`.
    have h_le := h a
    -- Step 2.8: Note that `u` decomposes orthogonally as `(u + a • v) + (-a) • v`.
    have h_ortho_neg : ⟪u + a • v, -a • v⟫_F = 0 := by
      -- Step 2.8.1: Orthogonality survives scaling in the second argument.
      simp [inner_smul_right, h_ortho_v]
    have h_pyth : ‖u‖ ^ 2 = ‖u + a • v‖ ^ 2 + ‖a • v‖ ^ 2 := by
      -- Step 2.8.2: Apply the Pythagorean theorem to the orthogonal decomposition of `u`.
      have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (u + a • v) (-a • v) (by
        simpa using h_ortho_neg)
      -- Step 2.8.2.1: Simplify the resulting expression to isolate `‖u‖ ^ 2` on the left.
      simpa [pow_two, add_comm, add_left_comm, add_assoc]
        using this
    -- Step 2.9: Show that the correction term `‖a • v‖ ^ 2` is strictly positive.
    have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha_ne
    have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have h_smul_pos : 0 < ‖a • v‖ := by
      -- Step 2.9.1: Use multiplicativity of the norm to combine `ha_pos` and `hv_pos`.
      simpa [norm_smul] using mul_pos ha_pos hv_pos
    have h_smul_sq_pos : 0 < ‖a • v‖ ^ 2 := sq_pos_of_pos h_smul_pos
    -- Step 2.10: Convert the Pythagorean identity into a strict inequality.
    have h_diff_pos : 0 < ‖u‖ ^ 2 - ‖u + a • v‖ ^ 2 := by
      -- Step 2.10.1: Rearrange `h_pyth` to express the difference as the positive square term.
      have : ‖u‖ ^ 2 - ‖u + a • v‖ ^ 2 = ‖a • v‖ ^ 2 := by
        simp [h_pyth, add_comm, add_assoc, sub_eq_add_neg]
      -- Step 2.10.2: Substitute the strictly positive square obtained above.
      simpa [this] using h_smul_sq_pos
    have h_lt_sq : ‖u + a • v‖ ^ 2 < ‖u‖ ^ 2 := sub_pos.mp h_diff_pos
    -- Step 2.11: Pull the strict inequality on squares back to norms.
    have h_lt_norm : ‖u + a • v‖ < ‖u‖ := by
      -- Step 2.11.1: Compare absolute values using strict monotonicity of squaring on nonnegatives.
      have h_abs_lt : |‖u + a • v‖| < |‖u‖| := (sq_lt_sq).1 h_lt_sq
      -- Step 2.11.2: Norms are nonnegative, so absolute values simplify directly.
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using h_abs_lt
    -- Step 2.12: Reach the contradiction with the assumed lower bound and finish the proof.
    exact (not_le_of_gt h_lt_norm) h_le
