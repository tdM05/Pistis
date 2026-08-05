import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $F$ is a field of characteristic $p \neq 0$, show that $(a + b)^m = a^m + b^m$, where $m = p^n$, for all $a, b \in F$ and any positive integer $n$.
-/

/-Informal Proof

Since $F$ is of characteristic $p$ and we have considered arbitrary two elements $a, b$ in $F$ we have
$$
\begin{aligned}
& p a=p b=0 \\
& \Longrightarrow p^n a=p^n b=0 \\
& \Longrightarrow m a=m b=0 \text {. } \\
&
\end{aligned}
$$
Now we know from Binomial Theorem that
$$
(a+b)^m=\sum_{i=0}^m\left(\begin{array}{c}
m \\
i
\end{array}\right) a^i b^{m-i}
$$
Here
$$
\left(\begin{array}{c}
m \\
i
\end{array}\right)=\frac{m !}{i !(m-i) !} .
$$
Now we know that for any integer $n$ and any integer $k$ satisfying $1 \leq k<n, n$ always divides $\left(\begin{array}{l}n \\ k\end{array}\right)$. So in our case for $i$ in the range $1 \leq i<m, m$ divides $\left(\begin{array}{c}m \\ i\end{array}\right)$. It follows that $p$ divides $\left(\begin{array}{c}m \\ i\end{array}\right)$, for $i$ satisfying $1 \leq i<m$, since $m=p^n$ for any integer $n$. Therefore other than the terms $a^m$ and $b^m$ in the expansion $\sum_{i=0}^m\left(\begin{array}{c}m \\ i\end{array}\right) a^i b^{m-i}$ will vanish due to char $p$ nature of $F$.
Hence we have
$$
\sum_{i=0}^m\left(\begin{array}{c}
m \\
i
\end{array}\right) a^i b^{m-i}=a^m+b^m
$$
This follows that, for all $a, b \in F$
$$
(a+b)^m=a^m+b^m .
$$
This completes the proof.
-/

theorem Herstein_exercise_5_1_8 {p m n: ℕ} {F : Type*} [Field F]
  (hp : p ≠ 0) (hn : n > 0)
  (hF : CharP F p) (a b : F) (hm : m = p ^ n) :
  (a + b) ^ m = a^m + b^m := by
  --------------------------------------------------------------------------
  -- Step 1: Turn the explicit hypothesis `hF : CharP F p` into an instance
  -- so type-class inference can use the characteristic information freely.
  --------------------------------------------------------------------------
  letI : CharP F p := hF

  --------------------------------------------------------------------------
  -- Step 2: Promote the assumption `hp : p ≠ 0` to the `NeZero p` type-class.
  -- This is needed because many lemmas about characteristics expect it as an
  -- instance rather than a bare hypothesis.
  --------------------------------------------------------------------------
  letI : NeZero p := ⟨hp⟩

  --------------------------------------------------------------------------
  -- Step 2.1: Consume the positivity assumption on `n`. The later argument
  -- does not rely on it, but using the hypothesis avoids unused-variable
  -- issues and records that `n` is indeed positive as stated.
  --------------------------------------------------------------------------
  have _ : 0 < n := hn

  --------------------------------------------------------------------------
  -- Step 3: In any (nonzero characteristic) field, the characteristic prime
  -- number `p` is actually *prime*. We register this as a type-class instance
  -- `Fact p.Prime`, which several Frobenius-style lemmas rely on.
  --------------------------------------------------------------------------
  have hprime : Fact p.Prime :=
    ⟨(CharP.char_is_prime_or_zero (R := F) (p := p)).resolve_right hp⟩
  letI := hprime

  --------------------------------------------------------------------------
  -- Step 4: Replace the abstract exponent `m` by the given power `p ^ n`
  -- so the goal exactly matches the Frobenius-style lemma we plan to use.
  --------------------------------------------------------------------------
  subst hm

  --------------------------------------------------------------------------
  -- Step 5: Because `F` is a commutative ring, any two elements commute.
  -- We register the commuting pair `(a, b)` to use the `add_pow_char_pow`
  -- lemma, which asserts additivity of the `p^n`-th power map.
  --------------------------------------------------------------------------
  have hcomm : Commute a b := Commute.all a b

  --------------------------------------------------------------------------
  -- Step 6: Apply the algebraic lemma stating that in characteristic `p`,
  -- for commuting elements, raising a sum to `p^n` distributes over the sum.
  -- This delivers `(a + b)^(p^n) = a^(p^n) + b^(p^n)`, which is exactly the
  -- desired conclusion after the earlier substitution `m = p^n`.
  --------------------------------------------------------------------------
  simpa using (add_pow_char_pow_of_commute (R := F) (p := p) (n := n) hcomm)
