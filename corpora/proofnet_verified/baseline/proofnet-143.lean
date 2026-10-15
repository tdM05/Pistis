import Mathlib

open scoped BigOperators


/-! # Pell-style helper sequences with step-by-step annotations -/

/- Step 0: Define the recursive Pell pairs `(x_n, y_n)` and their projections. -/
def pellPair : ℕ → ℕ × ℕ
  | 0 => (3, 2)
  | n + 1 =>
      let p := pellPair n
      (3 * p.1 + 4 * p.2, 2 * p.1 + 3 * p.2)

def pellX (n : ℕ) : ℕ := (pellPair n).1
def pellY (n : ℕ) : ℕ := (pellPair n).2

@[simp] lemma pellX_zero : pellX 0 = 3 := rfl
@[simp] lemma pellY_zero : pellY 0 = 2 := rfl

@[simp] lemma pellX_succ (n : ℕ) :
    pellX (n + 1) = 3 * pellX n + 4 * pellY n := by
  -- Step 1: unfold the recursive definition and project the first coordinate.
  simp [pellX, pellY, pellPair]

@[simp] lemma pellY_succ (n : ℕ) :
    pellY (n + 1) = 2 * pellX n + 3 * pellY n := by
  -- Step 1: unfold the recursive definition and project the second coordinate.
  simp [pellX, pellY, pellPair]

/- Step 1: Auxiliary polynomial identity capturing one Pell step. -/
lemma pellStep_identity (x y : ℤ) :
    (3 * x + 4 * y) ^ 2 - 2 * (2 * x + 3 * y) ^ 2 = x ^ 2 - 2 * y ^ 2 := by
  -- Step 1.1: the equality is purely algebraic, so `ring` settles it directly.
  ring

/- Step 2: Transfer the Pell invariant into the integer world for easier algebra. -/
lemma pellInvariant_int (n : ℕ) :
    (pellX n : ℤ) ^ 2 - 2 * (pellY n : ℤ) ^ 2 = 1 := by
  -- Step 2.1: proceed by induction on `n`.
  induction' n with k hk
  · -- Step 2.1.1: base case corresponds to the seed pair `(3, 2)`.
    norm_num
  · -- Step 2.1.2: prepare convenient abbreviations.
    set x : ℤ := (pellX k : ℤ)
    set y : ℤ := (pellY k : ℤ)
    have hx : (pellX (k + 1) : ℤ) = 3 * x + 4 * y := by
      -- Step 2.1.2.1: coerce the recursive formula to `ℤ` and simplify.
      simp [x, y, Nat.cast_add, Nat.cast_mul]
    have hy : (pellY (k + 1) : ℤ) = 2 * x + 3 * y := by
      -- Step 2.1.2.2: analogous coercion for the `y`-coordinate.
      simp [x, y, Nat.cast_add, Nat.cast_mul]
    -- Step 2.1.2.3: use the algebraic identity to relate successive differences.
    have hstep :
        (pellX (k + 1) : ℤ) ^ 2 - 2 * (pellY (k + 1) : ℤ) ^ 2 =
          x ^ 2 - 2 * y ^ 2 := by
      simpa [hx, hy] using pellStep_identity x y
    -- Step 2.1.2.4: conclude via the inductive hypothesis.
    simpa [x, y] using hstep.trans hk

/- Step 3: bring the Pell invariant back to `ℕ`. -/
lemma pellInvariant (n : ℕ) :
    pellX n ^ 2 = 2 * pellY n ^ 2 + 1 := by
  -- Step 3.1: translate the integer equality using injectivity of the coercion.
  have hx := pellInvariant_int n
  have hx' : (pellX n : ℤ) ^ 2 = 2 * (pellY n : ℤ) ^ 2 + 1 := by
    -- Step 3.1.1: rearrange `hx` into a sum on the right-hand side.
    have := congrArg (fun t => t + 2 * (pellY n : ℤ) ^ 2) hx
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
  -- Step 3.1.2: remove the coercions to get back to natural numbers.
  exact_mod_cast hx'

/- Step 4: capture the simple ≥3 growth of the `y_n` sequence. -/
lemma pellY_succ_ge_three_mul (n : ℕ) :
    3 * pellY n ≤ pellY (n + 1) := by
  -- Step 4.1: from the closed form of `pellY (n + 1)` we drop the nonnegative term.
  have : 3 * pellY n ≤ 3 * pellY n + 2 * pellX n := Nat.le_add_right _ _
  simpa [pellY_succ, add_comm, add_left_comm, add_assoc, two_mul,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using this

lemma pellY_linear (n : ℕ) : 2 * n + 2 ≤ pellY n := by
  -- Step 4.2: a simple linear lower bound obtained from the ≥3 growth.
  induction' n with k hk
  · simp
  · have hcompare : 2 * (k + 1) + 2 ≤ 3 * (2 * k + 2) := by
      -- Step 4.2.1: pad the left-hand side by a manifestly nonnegative amount.
      have hbase :
          2 * (k + 1) + 2 ≤ 2 * (k + 1) + 2 + (4 * k + 2) :=
        Nat.le_add_right _ _
      -- Step 4.2.2: rewrite the right-hand side via a tidy algebraic identity.
      have hrewrite :
          2 * (k + 1) + 2 + (4 * k + 2) = 3 * (2 * k + 2) := by
        -- Step 4.2.2.1: `ring` expands both sides over the semiring `ℕ`.
        ring
      -- Step 4.2.3: conclude the comparison via the rewritten inequality.
      simpa [hrewrite] using hbase
    have hx : 3 * (2 * k + 2) ≤ 3 * pellY k := Nat.mul_le_mul_left 3 hk
    exact le_trans (le_trans hcompare hx) (pellY_succ_ge_three_mul k)

lemma quadratic_bound (n : ℕ) : n + 2 ≤ 2 * (2 * n + 2) ^ 2 := by
  -- Step 5: a quadratic lower bound that dominates `n`.
  have h1 : n + 2 ≤ 2 * n + 2 := by
    simp [two_mul, add_assoc]
  have hpos : 1 ≤ 2 * n + 2 := by
    have : 0 ≤ 2 * n + 1 := Nat.zero_le _
    exact Nat.succ_le_succ this
  have h2 : 2 * n + 2 ≤ (2 * n + 2) ^ 2 := by
    have := Nat.mul_le_mul_left (2 * n + 2) hpos
    simp [pow_two]
  have h3 : (2 * n + 2) ^ 2 ≤ 2 * (2 * n + 2) ^ 2 := by
    have := Nat.le_add_left ((2 * n + 2) ^ 2) ((2 * n + 2) ^ 2)
    simp [two_mul]
  exact le_trans h1 (le_trans h2 h3)







/-Informal Statement

Prove that there exist infinitely many integers $n$ such that $n, n+1, n+2$ are each the sum of the squares of two integers.
-/

/-Informal Proof

It is well-known that the equation $x^2-2y^2=1$ has infinitely
many solutions (the so-called ``Pell'' equation).  Thus setting
$n=2y^2$ (so that $n=y^2+y^2$, $n+1=x^2+0^2$, $n+2=x^2+1^2$)
yields infinitely many $n$ with the desired property.
-/

theorem Putnam_exercise_2000_a2 :
  ∀ N : ℕ, ∃ n : ℕ, n > N ∧ ∃ i : Fin 6 → ℕ, n = (i 0)^2 + (i 1)^2 ∧
  n + 1 = (i 2)^2 + (i 3)^2 ∧ n + 2 = (i 4)^2 + (i 5)^2 := by
  -- Step 0: enable classical reasoning for the upcoming finite function literal.
  classical
  -- Step 1: introduce an arbitrary bound `N`.
  intro N
  -- Step 1.1: set up the Pell indices and the eventual candidate `n`.
  let k : ℕ := N + 1
  let x : ℕ := pellX k
  let y : ℕ := pellY k
  let nVal : ℕ := 2 * y ^ 2
  -- Step 1.2: show that `nVal` dominates the bound `N`.
  have hsize : 2 * k + 2 ≤ y := by
    simpa [x, y] using pellY_linear k
  have hy_sq : (2 * k + 2) ^ 2 ≤ y ^ 2 := by
    have := Nat.mul_le_mul hsize hsize
    simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hbound : 2 * (2 * k + 2) ^ 2 ≤ nVal := by
    have := Nat.mul_le_mul_left (2 : ℕ) hy_sq
    simpa [nVal, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hNlin : N + 3 ≤ nVal := by
    -- Step 1.2.1: combine the quadratic bounds.
    have hk := quadratic_bound k
    have := le_trans hk hbound
    simpa [k, add_comm, add_left_comm, add_assoc] using this
  have hstep : N < N + 3 := by
    -- Step 1.2.2: a simple additivity argument shows `N < N + 3`.
    simp
  have hNlt : N < nVal :=
    -- Step 1.2.3: deduce the strict inequality from the linear bound.
    lt_of_lt_of_le hstep hNlin
  -- Step 2: package the numerical witness `nVal` and prepare the square decompositions.
  refine ⟨nVal, hNlt, ?_⟩
  -- Step 2.1: define the six-term witness vector.
  let i : Fin 6 → ℕ := ![y, y, x, 0, x, 1]
  refine ⟨i, ?_⟩
  -- Step 2.2: record the Pell equation relating `x` and `y`.
  have hx_sq : x ^ 2 = 2 * y ^ 2 + 1 := by
    simpa [x, y] using pellInvariant k
  -- Step 2.3: verify the three required identities sequentially.
  refine ⟨?_, ?_⟩
  · -- Step 2.3.1: `nVal` itself is twice `y^2`, hence the sum of two identical squares.
    simp [nVal, two_mul, i]
  · -- Step 2.3.2: handle the `n + 1` and `n + 2` constraints.
    refine ⟨?_, ?_⟩
    · -- Step 2.3.2.1: `n + 1` coincides with `x^2` by the Pell invariant.
      have hgoal : nVal + 1 = x ^ 2 := by
        -- Step 2.3.2.1.1: rewrite the left-hand side in terms of `y`.
        calc
          nVal + 1 = 2 * y ^ 2 + 1 := by simp [nVal]
          _ = x ^ 2 := by simpa using hx_sq.symm
      simpa [i] using hgoal
    · -- Step 2.3.2.2: `n + 2` equals `x^2 + 1` because `x^2 = 2y^2 + 1`.
      have hxplus : x ^ 2 + 1 = 2 * y ^ 2 + 2 := by
        -- Step 2.3.2.2.1: apply the Pell identity and then reassociate the tail.
        have hxplus0 : x ^ 2 + 1 = (2 * y ^ 2 + 1) + 1 := by
          simp [hx_sq]
        have hxplus1 : (2 * y ^ 2 + 1) + 1 = 2 * y ^ 2 + 2 := by
          -- Step 2.3.2.2.1.1: reassociate and convert `1 + 1` into `2`.
          calc
            (2 * y ^ 2 + 1) + 1 = 2 * y ^ 2 + (1 + 1) := by
              simp [add_assoc]
            _ = 2 * y ^ 2 + 2 := by simp [one_add_one_eq_two]
        exact hxplus0.trans hxplus1
      have hgoal : nVal + 2 = x ^ 2 + 1 := by
        -- Step 2.3.2.2.2: rewrite through `hxplus`.
        have hleft : nVal + 2 = 2 * y ^ 2 + 2 := by simp [nVal]
        exact hleft.trans hxplus.symm
      simpa [i] using hgoal
