import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

A ring $R$ is called a Boolean ring if $a^{2}=a$ for all $a \in R$. Prove that every Boolean ring is commutative.
-/

/-Informal Proof

Solution: Note first that for all $a \in R$,
$$
-a=(-a)^2=(-1)^2 a^2=a^2=a .
$$
Now if $a, b \in R$, we have
$$
a+b=(a+b)^2=a^2+a b+b a+b^2=a+a b+b a+b .
$$
Thus $a b+b a=0$, and we have $a b=-b a$. But then $a b=b a$. Thus $R$ is commutative.
-/

theorem Dummit_Foote_exercise_7_1_15 {R : Type*} [Ring R] (hR : ∀ a : R, a^2 = a) :
∀ a b : R, a*b = b*a := by
  -- Step 1: show every element is its own additive inverse (`-a = a`).
  have h_neg : ∀ a : R, -a = a := by
    -- Step 1.1: apply idempotency to the element `-a`.
    intro a
    have h1 : (-a)^2 = -a := hR (-a)
    -- Step 1.2: rewrite `(-a)^2` as `a * a` using basic ring simplifications.
    have h1' : a * a = -a := by
      simpa [pow_two] using h1
    -- Step 1.3: rewrite `a^2` as `a` using the given hypothesis.
    have h2' : a * a = a := by
      simpa [pow_two] using hR a
    -- Step 1.4: combine the two equalities to obtain `-a = a`.
    calc
      -a = a * a := by
        symm
        exact h1'
      _ = a := h2'

  -- Step 2: deduce that doubling any element is zero (`a + a = 0`).
  have h_two : ∀ a : R, a + a = 0 := by
    intro a
    -- Step 2.1: start from `-a = a` and add `a` to both sides.
    have h' := congrArg (fun x => x + a) (h_neg a)
    -- Step 2.2: simplify `-a + a` to `0` to obtain `0 = a + a`.
    have h'' : 0 = a + a := by
      simpa using h'
    -- Step 2.3: flip the equality to get the desired orientation.
    simpa [add_comm] using h''.symm

  -- Step 3: prove commutativity by examining the square of a sum.
  intro a b
  -- Step 3.1: expand `(a + b)^2` explicitly.
  have h_expand : (a + b)^2 = a * a + a * b + b * a + b * b := by
    -- Step 3.1.1: replace the power by a product.
    calc
      (a + b)^2 = (a + b) * (a + b) := by
        simp [pow_two]
      _ = a * (a + b) + b * (a + b) := by
        -- distribute the right factor over the left sum.
        simpa using add_mul a b (a + b)
      _ = (a * a + a * b) + (b * a + b * b) := by
        -- distribute the left factor over the right sum in each addend.
        simp [mul_add, add_assoc]
      _ = a * a + a * b + b * a + b * b := by
        -- reassociate to a flat sum.
        simp [add_assoc]

  -- Step 3.2: simplify the expanded equality using the idempotent property for `a` and `b`.
  have ha : a * a = a := by
    -- Step 3.2.1: direct consequence of `hR` applied to `a`.
    simpa [pow_two] using hR a
  have hb : b * b = b := by
    -- Step 3.2.2: direct consequence of `hR` applied to `b`.
    simpa [pow_two] using hR b

  -- Step 3.3: rewrite `(a + b)^2 = a + b` with the expanded form and simplify.
  have h_eq : a + a * b + b * a + b = a + b := by
    -- Step 3.3.1: start from the given equality `(a + b)^2 = a + b`.
    have h_sq : (a + b)^2 = a + b := hR (a + b)
    -- Step 3.3.2: substitute the explicit expansion of `(a + b)^2`.
    have h_sq' : a * a + a * b + b * a + b * b = a + b := by
      simpa [h_expand] using h_sq
    -- Step 3.3.3: replace `a * a` and `b * b` with `a` and `b` respectively.
    simpa [ha, hb, add_assoc] using h_sq'

  -- Step 3.4: isolate the mixed terms to obtain `a * b + b * a = 0`.
  have h_mixed : a * b + b * a = 0 := by
    -- Step 3.4.1: rewrite `h_eq` so that the leading `a` is isolated.
    have h1 : a + (a * b + b * a + b) = a + b := by
      calc
        a + (a * b + b * a + b) = a + a * b + b * a + b := by
          simp [add_assoc]
        _ = a + b := h_eq
    -- Step 3.4.2: cancel the leading `a` from both sides.
    have h2 : a * b + b * a + b = b := by
      exact add_left_cancel h1
    -- Step 3.4.3: rewrite the right side as `0 + b` to cancel `b` on the right.
    have h2' : a * b + b * a + b = 0 + b := by
      simpa using h2
    -- Step 3.4.4: cancel the trailing `b` from both sides to isolate the mixed terms.
    have h3 : a * b + b * a = 0 := by
      exact add_right_cancel h2'
    -- Step 3.4.5: register the resulting equality.
    exact h3

  -- Step 3.5: convert `a * b + b * a = 0` into `a * b = b * a` using characteristic two.
  have h_comm : a * b = b * a := by
    -- Step 3.5.1: from `h_mixed` we know `a * b = -(b * a)`.
    have h_neg_ba : a * b = -(b * a) := eq_neg_of_add_eq_zero_left h_mixed
    -- Step 3.5.2: but `-(b * a)` equals `b * a` thanks to `h_neg`.
    have h_self : -(b * a) = b * a := h_neg (b * a)
    -- Step 3.5.3: combine the two equalities.
    exact h_neg_ba.trans h_self

  -- Step 3.6: return the desired commutativity statement.
  exact h_comm
