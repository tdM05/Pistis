import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $R$ is a commutative ring and $a \in R$, let $L(a) = \{x \in R \mid xa = 0\}$. Prove that $L(a)$ is an ideal of $R$.
-/

/-Informal Proof

First, note that if $x \in L(a)$ and $y \in L(a)$ then $x a=0$ and $y a=0$, so that
$$
\begin{aligned}
x a-y a & =0 \\
(x-y) a & =0,
\end{aligned}
$$
i.e. $L(a)$ is an additive subgroup of $R$. (We have used the criterion that $H$ is a subgroup of $G$ if for any $h_1, h_2 \in H$ we have that $h_1 h_2^{-1} \in H$. 

Now we prove the conclusion. Let $r \in R$ and $b \in L(a)$, then $b a=0$, and so $x b a=0$ which by associativity of multiplication in $R$ is equivalent to
$$
(x b) a=0,
$$
so that $x b \in L(a)$. Since $R$ is commutative, (1) implies that $(bx)a=0$, so that $b x \in L(a)$, which concludes the proof that $L(a)$ is an ideal.
-/

theorem Herstein_exercise_4_3_1 {R : Type*} [CommRing R] (a : R) :
  ∃ I : Ideal R, {x : R | x*a=0} = I := by
  -- Step 1: Exhibit an explicit candidate ideal consisting of all annihilators of `a`.
  refine ⟨
    { carrier := { x : R | x * a = 0 }
      -- Step 1.1: Verify that `0` belongs to the set because it obviously annihilates `a`.
      zero_mem' := by
        -- Step 1.1.1: Evaluate the defining equation at zero and simplify.
        simp
      -- Step 2: Show that the set is closed under addition, making it an additive subgroup.
      add_mem' := by
        -- Step 2.1: Introduce two annihilators `x` and `y` of `a`.
        intro x y hx hy
        -- Step 2.2: Register the equations `x * a = 0` and `y * a = 0` extracted from membership.
        have hx0 : x * a = 0 := hx
        have hy0 : y * a = 0 := hy
        -- Step 2.3: Expand `(x + y) * a` via distributivity and substitute the equalities.
        simp [add_mul, hx0, hy0]
      -- Step 3: Show closure under multiplication by arbitrary ring elements (ideal condition).
      smul_mem' := by
        -- Step 3.1: Introduce a scalar `r` and an element `x` annihilating `a`.
        intro r x hx
        -- Step 3.2: Record the equation `x * a = 0` coming from the hypothesis.
        have hx0 : x * a = 0 := hx
        -- Step 3.3: Rewrite `(r • x) * a` as `(r * x) * a`, reassociate, and substitute `hx0`.
        simp [smul_eq_mul, mul_assoc, hx0] },
    -- Step 4: Observe that, by construction, the underlying set of this ideal matches the target set.
    rfl⟩
