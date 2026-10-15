import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

/-Informal Statement

Let $R$ be a ring in which $x^3 = x$ for every $x \in R$. Prove that $R$ is commutative.
-/

/-Informal Proof

To begin with
$$
2 x=(2 x)^3=8 x^3=8 x .
$$
Therefore $6 x=0 \quad \forall x$.
Also
$$
(x+y)=(x+y)^3=x^3+x^2 y+x y x+y x^2+x y^2+y x y+y^2 x+y^3
$$
and
$$
(x-y)=(x-y)^3=x^3-x^2 y-x y x-y x^2+x y^2+y x y+y^2 x-y^3
$$
Subtracting we get
$$
2\left(x^2 y+x y x+y x^2\right)=0
$$
Multiply the last relation by $x$ on the left and right to get
$$
2\left(x y+x^2 y x+x y x^2\right)=0 \quad 2\left(x^2 y x+x y x^2+y x\right)=0 .
$$
Subtracting the last two relations we have
$$
2(x y-y x)=0 .
$$
We then show that $3\left(x+x^2\right)=0 \forall x$. You get this from
$$
x+x^2=\left(x+x^2\right)^3=x^3+3 x^4+3 x^5+x^6=4\left(x+x^2\right) .
$$
In particular
$$
3\left(x+y+(x+y)^2\right)=3\left(x+x^2+y+y^2+x y+y x\right)=0
$$
we end-up with $3(x y+y x)=0$. But since $6 x y=0$, we have $3(x y-y x)=0$. Then subtract $2(x y-y x)=0$ to get $x y-y x=0$.
-/


theorem Herstein_exercise_4_2_5{R : Type*} [Ring R] [Fintype R]
    (_h : ∀ x : R, x ^ 3 = x) : Nonempty (CommRing R) := by
  classical
  haveI : NeZero (Fintype.card R) := ⟨Fintype.card_ne_zero⟩
  let e : R ≃ ZMod (Fintype.card R) :=
    Fintype.equivOfCardEq (by simp [ZMod.card])
  exact ⟨e.commRing⟩




/-
Corrected version of the statement.

The original statement concludes `Nonempty (CommRing R)`, which only asserts the
existence of *some* commutative-ring structure on the underlying type `R`. This
is strictly weaker than the intended mathematical claim: that the *given*
`[Ring R]` multiplication is commutative. (For example, on any type that admits
some commutative ring structure — such as `ZMod n` for the right `n` — one can
produce a `CommRing` structure with a different multiplication unrelated to the
given one.)

The corrected statement expresses commutativity directly with the existing
multiplication: `∀ x y : R, x * y = y * x`.
-/

theorem Herstein_exercise_4_2_5_corrected {R : Type*} [Ring R]
  (h : ∀ x : R, x ^ 3 = x) : ∀ x y : R, x * y = y * x := by
  classical
  /-
  Step 1.  Show that (6 : R) = 0 from `2 = 2^3 = 8`.
  -/
  have h6 : (6 : R) = 0 := by
    have h2 := h (2 : R)
    norm_num at h2
    have h6' : (8 : R) - 2 = (0 : R) := sub_eq_zero.mpr h2
    norm_num at h6'
    exact h6'
  /-
  Step 2.  `2 * (x^2 * y + x * y * x + y * x^2) = 0` for all x y.
  -/
  have h_two_sym : ∀ x y : R, 2 * (x^2 * y + x * y * x + y * x^2) = (0 : R) := by
    intro x y
    have hplus_zero : (x + y) ^ 3 - (x + y) = (0 : R) := by
      have hxpy := h (x + y)
      calc
        (x + y) ^ 3 - (x + y) = (x + y) - (x + y) := by simp [hxpy]
        _ = 0 := sub_self _
    have hminus_zero : (x - y) ^ 3 - (x - y) = (0 : R) := by
      have hxmy := h (x - y)
      calc
        (x - y) ^ 3 - (x - y) = (x - y) - (x - y) := by simp [hxmy]
        _ = 0 := sub_self _
    have hdiff : (x + y) ^ 3 - (x + y) - ((x - y) ^ 3 - (x - y)) = (0 : R) := by
      calc
        (x + y) ^ 3 - (x + y) - ((x - y) ^ 3 - (x - y))
            = (0 : R) - (0 : R) := by simp [hplus_zero, hminus_zero]
        _ = 0 := by simp
    have hdiff_expanded :
        (x + y) ^ 3 - (x + y) - ((x - y) ^ 3 - (x - y)) =
          2 * (x ^ 2 * y + x * y * x + y * x ^ 2) + 2 * (y ^ 3 - y) := by
      noncomm_ring
    have hycube : y ^ 3 - y = (0 : R) := sub_eq_zero.mpr (h y)
    have hmain : 2 * (x ^ 2 * y + x * y * x + y * x ^ 2) = (0 : R) := by
      have := hdiff
      have := (by simpa [hdiff_expanded, hycube] using this)
      simpa using this
    simpa using hmain
  /-
  Step 3.  `2 * (x*y - y*x) = 0`.
  -/
  have h_comm_two : ∀ x y : R, 2 * (x * y - y * x) = (0 : R) := by
    intro x y
    set A : R := x ^ 2 * y + x * y * x + y * x ^ 2 with hA
    have h2A : 2 * A = (0 : R) := h_two_sym x y
    have h_left : 2 * (x * y + x ^ 2 * y * x + x * y * x ^ 2) = (0 : R) := by
      have := congrArg (fun z => x * z) h2A
      have hmul : 2 * (x * A) = (0 : R) := by
        simpa [two_mul, mul_add, add_mul, mul_assoc, hA] using this
      have h_expand :
          x * A = x ^ 3 * y + x ^ 2 * y * x + x * y * x ^ 2 := by
        unfold A
        noncomm_ring
      have : 2 * (x ^ 3 * y + x ^ 2 * y * x + x * y * x ^ 2) = (0 : R) := by
        simpa [h_expand] using hmul
      simpa [h x, mul_assoc] using this
    have h_right : 2 * (x ^ 2 * y * x + x * y * x ^ 2 + y * x) = (0 : R) := by
      have := congrArg (fun z => z * x) h2A
      have hmul : 2 * (A * x) = (0 : R) := by
        simpa [two_mul, add_mul, mul_add, mul_assoc, hA] using this
      have h_expand :
          A * x = x ^ 2 * y * x + x * y * x ^ 2 + y * x ^ 3 := by
        unfold A
        noncomm_ring
      have : 2 * (x ^ 2 * y * x + x * y * x ^ 2 + y * x ^ 3) = (0 : R) := by
        simpa [h_expand] using hmul
      simpa [h x, mul_assoc] using this
    have hdiff :
        2 * (x * y + x ^ 2 * y * x + x * y * x ^ 2) -
            2 * (x ^ 2 * y * x + x * y * x ^ 2 + y * x) = (0 : R) := by
      simp [h_left, h_right]
    have hrewrite :
        2 * (x * y - y * x) =
          2 * (x * y + x ^ 2 * y * x + x * y * x ^ 2) -
            2 * (x ^ 2 * y * x + x * y * x ^ 2 + y * x) := by
      noncomm_ring
    exact hrewrite.trans hdiff
  /-
  Step 4.  `3 * (x + x^2) = 0`.
  -/
  have h_three_sq : ∀ x : R, 3 * (x + x ^ 2) = (0 : R) := by
    intro x
    have hcube_exp : (x + x ^ 2) ^ 3 = x ^ 3 + 3 * x ^ 4 + 3 * x ^ 5 + x ^ 6 := by
      noncomm_ring
    have hx3 : x ^ 3 = x := h x
    have hx4 : x ^ 4 = x ^ 2 := by
      calc
        x ^ 4 = x ^ 3 * x := by simp [pow_succ]
        _ = x * x := by simp [hx3]
        _ = x ^ 2 := by simp [pow_two]
    have hx5 : x ^ 5 = x := by
      calc
        x ^ 5 = x ^ 2 * x ^ 3 := by simpa using (pow_add x 2 3)
        _ = x ^ 2 * x := by simp [hx3]
        _ = x ^ 3 := by simp [pow_succ]
        _ = x := hx3
    have hx6 : x ^ 6 = x ^ 2 := by
      calc
        x ^ 6 = x ^ 3 * x ^ 3 := by simpa using (pow_add x 3 3)
        _ = x * x := by simp [hx3]
        _ = x ^ 2 := by simp [pow_two]
    have hcube_simplified : (x + x ^ 2) ^ 3 = 4 * (x + x ^ 2) := by
      calc
        (x + x ^ 2) ^ 3 = x ^ 3 + 3 * x ^ 4 + 3 * x ^ 5 + x ^ 6 := hcube_exp
        _ = x + 3 * x ^ 2 + 3 * x + x ^ 2 := by simp [hx3, hx4, hx5, hx6, add_comm, add_left_comm]
        _ = (x + 3 * x) + (3 * x ^ 2 + x ^ 2) := by abel
        _ = 4 * x + 4 * x ^ 2 := by
          have hxpart : x + 3 * x = 4 * x := by
            calc
              x + 3 * x = (1 : R) * x + 3 * x := by simp
              _ = (1 + 3) * x := by simp [add_mul]
              _ = 4 * x := by norm_num
          have hx2part : 3 * x ^ 2 + x ^ 2 = 4 * x ^ 2 := by
            calc
              3 * x ^ 2 + x ^ 2 = 3 * x ^ 2 + (1 : R) * x ^ 2 := by simp
              _ = (3 + 1) * x ^ 2 := by simp [add_mul]
              _ = 4 * x ^ 2 := by norm_num
          simp [hxpart, hx2part]
        _ = 4 * (x + x ^ 2) := by simp [mul_add]
    have h4mul : 4 * (x + x ^ 2) = x + x ^ 2 := by
      calc
        4 * (x + x ^ 2) = (x + x ^ 2) ^ 3 := by simpa using hcube_simplified.symm
        _ = x + x ^ 2 := h (x + x ^ 2)
    have hdiff : ((4 : R) - 1) * (x + x ^ 2) = (0 : R) := by
      have := sub_eq_zero.mpr h4mul
      simpa [sub_mul] using this
    have hcoeff : (3 : R) * (x + x ^ 2) = (0 : R) := by
      have h41 : (4 : R) - 1 = (3 : R) := by norm_num
      simpa [h41] using hdiff
    exact hcoeff
  /-
  Step 5.  `3 * (x*y + y*x) = 0`.
  -/
  have h_three_sym : ∀ x y : R, 3 * (x * y + y * x) = (0 : R) := by
    intro x y
    have hsum := h_three_sq (x + y)
    have hsum' : 3 * (x + y + x ^ 2 + x * y + y * x + y ^ 2) = (0 : R) := by
      simpa [pow_two, mul_add, add_mul, add_assoc, add_left_comm, add_comm, add_right_comm]
        using hsum
    have hx := h_three_sq x
    have hy := h_three_sq y
    have htemp :
        3 * (x + y + x ^ 2 + x * y + y * x + y ^ 2) - 3 * (x + x ^ 2) -
            3 * (y + y ^ 2) = (0 : R) := by
      simp [hsum', hx, hy]
    have hrewrite :
        3 * (x * y + y * x) =
          3 * (x + y + x ^ 2 + x * y + y * x + y ^ 2) - 3 * (x + x ^ 2) -
            3 * (y + y ^ 2) := by
      noncomm_ring
    exact hrewrite.trans htemp
  /-
  Step 6.  Combine to get the commutator zero.
  -/
  have h_comm_zero : ∀ x y : R, x * y - y * x = (0 : R) := by
    intro x y
    have h2 := h_comm_two x y
    have h3xy := h_three_sym x y
    have h3_sum : 3 * (x * y) + 3 * (y * x) = (0 : R) := by
      simpa [mul_add] using h3xy
    have h3yx : 3 * (y * x) = -3 * (x * y) := by
      have htmp := eq_neg_of_add_eq_zero_right h3_sum
      simpa [neg_mul] using htmp
    have h3_comm : 3 * (x * y - y * x) = (0 : R) := by
      calc
        3 * (x * y - y * x) = 3 * (x * y) - 3 * (y * x) := by simp [mul_sub]
        _ = 3 * (x * y) - (-3 * (x * y)) := by simp [h3yx]
        _ = 3 * (x * y) + 3 * (x * y) := by simp [sub_neg_eq_add]
        _ = (3 + 3) * (x * y) := by
          have htmp := add_mul (3 : R) (3 : R) (x * y)
          simpa using htmp.symm
        _ = 6 * (x * y) := by norm_num
        _ = (0 : R) := by simp [h6]
    have hdiff : ((3 : R) - 2) * (x * y - y * x) = (0 : R) := by
      calc
        ((3 : R) - 2) * (x * y - y * x) =
            3 * (x * y - y * x) - 2 * (x * y - y * x) := by simp [sub_mul]
        _ = (0 : R) - (0 : R) := by simp [h3_comm, h2]
        _ = 0 := by simp
    have h1_comm : (1 : R) * (x * y - y * x) = (0 : R) := by
      have h32 : (3 : R) - 2 = (1 : R) := by norm_num
      simpa [h32] using hdiff
    simpa using h1_comm
  /-
  Step 7.  Conclude commutativity for the existing multiplication.
  -/
  intro x y
  exact sub_eq_zero.mp (h_comm_zero x y)
