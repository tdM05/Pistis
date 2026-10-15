import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

If $a, b$ are integers and if $a$ divides $b$ in the ring of Gauss integers, then $a$ divides $b$ in $\mathbb{Z}$.
-/

/-Informal Proof

Suppose $a|b$ in $\mathbb{Z}[i]$ and $a,b\in\mathbb{Z}$. Then $a(x+yi)=b$ for $x,y\in\mathbb{Z}$. Expanding this we get $ax+ayi=b$, and equating imaginary parts gives us $ay=0$, implying $y=0$.
-/

theorem Artin_exercise_11_2_13 (a b : ℤ) :
  (ofInt a : GaussianInt) ∣ ofInt b → a ∣ b := by
  classical
  -- Step 1: Introduce the hypothesis that `(ofInt a)` divides `(ofInt b)` in `ℤ[i]`.
  intro h
  -- Step 2: Unpack the divisibility assumption to obtain a Gaussian integer witness `z`.
  rcases h with ⟨z, hz⟩
  -- Step 3: Separate the proof into the special case `a = 0` and the nonzero case.
  by_cases ha : a = 0
  · -- Step 3.1: When `a = 0`, the equality in `ℤ[i]` forces `ofInt b = 0`.
    have hbGaussianZero : (ofInt b : GaussianInt) = 0 := by
      -- Step 3.1.1: Substitute `a = 0` into the equality and simplify to get `ofInt b = 0`.
      simpa [ha] using hz
    -- Step 3.1.2: Taking real parts shows that `b = 0` as integers.
    have hbzero : b = 0 := by
      -- Step 3.1.2.1: Real parts of `ofInt b` and `0` are just `b` and `0` respectively.
      simpa using congrArg (fun w : GaussianInt => w.re) hbGaussianZero
    -- Step 3.1.3: Exhibit the required witness (namely 0) for `0 ∣ 0`.
    exact ⟨0, by simp [ha, hbzero]⟩
  · -- Step 4: Work under the standing assumption `a ≠ 0` and force the witness to be real.
    -- Step 4.1: Compare imaginary parts to conclude that `z.im = 0`.
    have hmulZero : a * z.im = 0 := by
      -- Step 4.1.1: Imaginary parts match, so `0 = a * z.im`, which we rewrite symmetrically.
      have himEq : 0 = a * z.im := by
        simpa [im_ofInt, im_mul, re_ofInt] using
          congrArg (fun w : GaussianInt => w.im) hz
      simpa [eq_comm] using himEq
    -- Step 4.1.2: Since `a ≠ 0`, the previous equality implies `z.im = 0`.
    have zimZero : z.im = 0 :=
      (mul_eq_zero.mp hmulZero).resolve_left ha
    -- Step 4.2: Compare real parts to obtain an explicit integer witness for the divisibility.
    have hreEq : b = a * z.re := by
      -- Step 4.2.1: Real parts of the equality yield `b = a * z.re` because the imaginary part vanishes.
      simpa [re_ofInt, im_ofInt, re_mul, zimZero] using
        congrArg (fun w : GaussianInt => w.re) hz
    -- Step 4.3: Conclude divisibility in `ℤ` using the witness `z.re`.
    exact ⟨z.re, hreEq⟩
