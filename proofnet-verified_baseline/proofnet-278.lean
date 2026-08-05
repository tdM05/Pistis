import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $F$ is of characteristic $p \neq 0$, show that all the roots of $x^m - x$, where $m = p^n$, are distinct.
-/

/-Informal Proof

Let us consider $f(x)=x^m-x$. Then $f \in F[x]$.
Claim: $f(x)$ has a multiple root in some extension of $F$ if and only if $f(x)$ is not relatively prime to its formal derivative, $f^{\prime}(x)$. 

Proof of the Claim: Let us assume that $f(x)$ has a multiple root in some extension of $F$. Let $y$ be a multiple root of $f(x)$. Then over a splitting field, we have
$$
f(x)=(x-y)^n g(x), \text { for some integer } n \geq 2 .
$$
Here $g(x)$ is a polynomial such that $g(y) \neq 0$. Now taking derivative of $f$ we get
$$
f^{\prime}(x)=n \cdot(x-y)^{n-1} g(x)+(x-y)^n g^{\prime}(x)
$$
here $g^{\prime}(x)$ implies derivative of $g$ with respect to $x$. Since we have $n \geq 2$, this implies $(n-1) \geq 1$. Hence, (1) shows that $f^{\prime}(x)$ has $y$ as a root. Therefore, $f(x)$ is not relatively prime to $f^{\prime}(x)$. We now prove the other direction.
Conversely, let us assume that $f(x)$ is not relatively prime to $f^{\prime}(x)$. Let $y$ is a root of both $f(x)$ and $f^{\prime}(x)$. Since $y$ is a root of $f(x)$, we can write
$$
f(x)=(x-y) \cdot g(x)
$$
for some polynomial $g(x)$. then taking derivative of $f(x)$ we have
$$
f^{\prime}(x)=g(x)+(x-y) \cdot g^{\prime}(x)
$$
where $g^{\prime}(x)$ is the derivative of $g(x)$ with respect to $x$. Since $y$ is a root of $f^{\prime}(x)$ also we have
$$
f^{\prime}(y)=0
$$
Then we have
$$
\begin{aligned}
& f^{\prime}(y)=g(y)+(y-y) \cdot g^{\prime}(y) \\
\Longrightarrow & f^{\prime}(y)=g(y) \\
\Longrightarrow & g(y)=0 .
\end{aligned}
$$
This implies $y$ is a root of $g(x)$ also. Therefore we have
$$
g(x)=(x-y) \cdot h(x)
$$
for some polynomial $h(x)$. Now form (2) we have
$$
f(x)=(x-y)^2 \cdot h(x) .
$$
This follows that $y$ is a multiple root of $f(x)$. Therefore, $f(x)$ has a multiple root in some extension of the field $F$. This completes the proof of the Claim.

In our case, $f(x)=x^m-x$, where $m=p^n$. Now we calculate the derivative of $f$. That is
$$
f^{\prime}(x)=m x^{m-1}-1=-1(\bmod p) .
$$
By the above condition it follows that, $f^{\prime}$ has no root same as $f$, that is, $f(x)$ and $f^{\prime}(x)$ are relatively prime. Hence, $f(x)$ has no multiple root in $F$. Since $f(x)=x^m-x$ is a polynomial of degree $m$, it follows that $f(x)$ has $m$ distinct roots in $F$, where $m=p^n$. This completes the proof.
-/

theorem Herstein_exercise_5_6_14 {p m n: ℕ} (hp : p ≠ 0) (hn : n > 0)
  {F : Type*} [Field F] [CharP F p] (hm : m = p ^ n) :
  (X ^ m - X : Polynomial F).Separable := by
  classical
  /- Step 0: from `hp` we record `p > 0`; this will be used for
     positivity facts about powers of `p`. -/
  have hp_pos : 0 < p := Nat.pos_of_ne_zero hp
  /- Step 1: show that `p ∣ m` because `m = p^n` with `n > 0`. -/
  have hdiv : p ∣ m := by
    -- Step 1.1: rewrite `m` using the given equality.
    subst hm
    -- Step 1.2: write `n = k.succ` using `n > 0`, so `p^n = p^(k.succ)`.
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    -- Step 1.3: exhibit the divisor `p^k` to show `p ∣ p^(k.succ)`.
    refine ⟨p ^ k, ?_⟩
    -- Step 1.4: simplify the power to a product, yielding the divisibility identity.
    simp [hk, Nat.pow_succ, Nat.mul_comm]
  /- Step 2: in characteristic `p`, the natural cast of any multiple of `p`
     is `0`. Hence `(m : F) = 0`. -/
  have hm_cast_zero : (m : F) = 0 :=
    (CharP.cast_eq_zero_iff (R := F) (p := p) m).2 hdiv
  /- Step 3: compute the formal derivative of `X^m - X`.
     Using `(m : F) = 0`, it collapses to the constant polynomial `-1`. -/
  have hder :
      derivative (X ^ m - X : Polynomial F) = (-1 : Polynomial F) := by
    -- Step 3.1: expand the derivative using linearity and the power rule.
    -- The cast `(m : F)` is `0` so the first term vanishes.
    simp [derivative_sub, derivative_X_pow, hm_cast_zero]
  /- Step 4: separability is defined as coprimality with the derivative.
     Since the derivative is the unit `-1`, we can write an explicit
     Bézout combination proving coprimality: `0 * f + (-1) * (-1) = 1`. -/
  refine (Polynomial.separable_def _).2 ?_
  -- Step 4.1: choose the Bézout coefficients `a = 0`, `b = -1`.
  refine ⟨0, (-1 : Polynomial F), ?_⟩
  -- Step 4.2: verify the Bézout identity after rewriting the derivative.
  -- The product `(-1) * (-1)` is `1`, so the sum equals `1`.
  simp [hder]
