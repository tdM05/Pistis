import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Prove that every nonzero ideal in the ring of Gauss integers contains a nonzero integer.
-/

/-Informal Proof

Let $I$ be some nonzero ideal. Then there exists some $z \in \mathbb{Z}[i], z \neq 0$ such that $z \in I$. We know that $z=a+b i$, for some $a, b \in \mathbb{Z}$. We consider three cases:
1. If $b=0$, then $z=a$, so $z \in \mathbb{Z} \cap I$, and $z \neq 0$, so the statement of the exercise holds.
2. If $a=0$, then $z=i b$. Since $z \neq 0$, we conclude that $b \neq 0$. Since $I$ is an ideal in $\mathbb{Z}[i]$, and $i \in \mathbb{Z}[i]$, we conclude that $i z \in I$. Furthermore, $i z=-b \in \mathbb{Z}$. Thus, $i z$ is a nonzero integer which is in $I$.
3. Let $a \neq 0$ and $b \neq 0$. Since $I$ is an ideal and $z \in I$, we conclude that $z^2 \in I$; that is,
$$
(a+b i)^2=a^2-b^2+2 a b i \in I
$$
Furthermore, since $-2 a \in \mathbb{Z}[i]$, and $z \in I$ and $I$ is an ideal, $-2 a z \in I$; that is,
$$
-2 a z=-2 a(a+b i)=-2 a^2-2 a b i \in I
$$
Since $I$ is closed under addition,
$$
\left(a^2-b^2+2 a b i\right)+\left(-2 a^2-2 a b i\right) \in I \Longrightarrow-a^2-b^2 \in I
$$
Notice that $-a^2-b^2 \neq 0$ since $a^2>0$ and $b^2>0$, so $-a^2-b^2<0$. Furthermore, it is an integer. Thus, we have found a nonzero integer in $I$.
-/

theorem Artin_exercise_10_6_7 {I : Ideal GaussianInt}
  (hI : I ≠ ⊥) : ∃ (z : I), z ≠ 0 ∧ (z : GaussianInt).im = 0 := by
  classical
  -- Step 1: Extract a nonzero element `g` inside `I` using the nontriviality assumption.
  obtain ⟨g, hg_mem, hg_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  -- Step 1.1: Record the witness `g` together with the proofs `hg_mem : g ∈ I` and `hg_ne : g ≠ 0`.
  -- Step 2: Form the product `w = g * star g`, which is expected to be an integer contained in `I`.
  let w : GaussianInt := g * star g
  -- Step 2.1: Show that `w` indeed lies in `I` because ideals are closed under multiplication by ring elements.
  have hw_mem : w ∈ I := by
    -- Step 2.1.1: First note that `star g * g` is in `I`, and then commute the factors.
    have h_aux : star g * g ∈ I := I.mul_mem_left (star g) hg_mem
    -- Step 2.1.2: Use commutativity to rewrite `star g * g` as `g * star g = w`.
    simpa [w, mul_comm] using h_aux
  -- Step 2.2: Prove that `w` is nonzero by showing each factor is nonzero.
  have hg_star_ne : star g ≠ (0 : GaussianInt) := by
    -- Step 2.2.1: If `star g = 0`, applying `star` again forces `g = 0`, contradicting `hg_ne`.
    intro h
    have : g = (0 : GaussianInt) := by
      -- Step 2.2.1.1: Apply `congrArg star` and simplify using `star_star`.
      simpa using congrArg star h
    exact hg_ne this
  -- Step 2.2.2: Combine the previous facts to deduce `w ≠ 0`.
  have hw_ne : w ≠ (0 : GaussianInt) := by
    -- Step 2.2.2.1: Apply `mul_ne_zero` to the two nonzero factors and rewrite the result as `w`.
    have : g * star g ≠ (0 : GaussianInt) := mul_ne_zero hg_ne hg_star_ne
    simpa [w] using this
  -- Step 3: Show that the imaginary part of `w` vanishes via the complex embedding, so `w` is an integer.
  have hComplex :
      ((w : GaussianInt) : ℂ) = Complex.normSq (g : ℂ) := by
    -- Step 3.1: Translate `w` to the complex numbers and recognize it as `g * conj g = ‖g‖²`.
    simpa [w, GaussianInt.toComplex_mul, GaussianInt.toComplex_star] using
      Complex.mul_conj (g : ℂ)
  -- Step 3.2: Take imaginary parts of both sides to deduce that the complex image of `w` is purely real.
  have hImComplex :
      (((w : GaussianInt) : ℂ).im = 0) := by
    -- Step 3.2.1: The right-hand side is a real number, so its imaginary part is zero.
    simpa using congrArg Complex.im hComplex
  -- Step 3.3: Translate the vanishing imaginary part back to the Gaussian integer level.
  have hw_im : w.im = 0 := by
    -- Step 3.3.1: Use `GaussianInt.intCast_im` to express `(w : ℂ).im` in terms of `w.im`.
    have hReal : (((w.im : ℤ) : ℝ)) = 0 := by
      simpa [GaussianInt.intCast_im] using hImComplex
    -- Step 3.3.2: Use injectivity of the integer-to-real embedding to conclude `w.im = 0`.
    exact_mod_cast hReal
  -- Step 4: Package the element `w` as an element of the ideal and record the required properties.
  refine ⟨⟨w, hw_mem⟩, ?_, ?_⟩
  -- Step 4.1: Prove that the element of `I` represented by `w` is nonzero.
  · -- Step 4.1.1: Equality in the subtype implies equality of the underlying values.
    intro hw_zero
    have : w = (0 : GaussianInt) := congrArg Subtype.val hw_zero
    exact hw_ne this
  -- Step 4.2: The imaginary part of the chosen element is zero by construction.
  · -- Step 4.2.1: Coercion from the subtype simply returns the value `w`.
    simpa [w] using hw_im
