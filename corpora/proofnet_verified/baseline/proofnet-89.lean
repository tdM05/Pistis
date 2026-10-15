import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $p$ is a prime, show that $q(x) = 1 + x + x^2 + \cdots x^{p - 1}$ is irreducible in $Q[x]$.
-/

/-Informal Proof

Lemma: Let $F$ be a field and $f(x) \in F[x]$. If $c \in F$ and $f(x+c)$ is irreducible in $F[x]$, then $f(x)$ is irreducible in $F[x]$.
Proof of the Lemma: Suppose that $f(x)$ is reducible, i.e., there exist non-constant $g(x), h(x) \in F[x]$ so that
$$
f(x)=g(x) h(x) .
$$
In particular, then we have
$$
f(x+c)=g(x+c) h(x+c) .
$$
Note that $g(x+c)$ and $h(x+c)$ have the same degree at $g(x)$ and $h(x)$ respectively; in particular, they are non-constant polynomials. So our assumption is wrong.
Hence, $f(x)$ is irreducible in $F[x]$. This proves our Lemma.

Now recall the identity
$$
\frac{x^p-1}{x-1}=x^{p-1}+x^{p-2}+\ldots \ldots+x^2+x+1 .
$$
We prove that $f(x+1)$ is $\$$ |textbffirreducible in $\mathbb{Q}[x]$ and then apply the Lemma to conclude that $f(x)$ is irreducible in $\mathbb{Q}[x] .3 \$$ Note that
$$
\begin{aligned}
& f(x+1)=\frac{(x+1)^p-1}{x} \\
& =\frac{x^p+p x^{p-1}+\ldots+p x}{x} \\
& =x^{p-1}+p x^{p-2}+\ldots .+p .
\end{aligned}
$$
Using that the binomial coefficients occurring above are all divisible by $p$, we have that $f(x+1)$ is irreducible $\mathbb{Q}[x]$ by Eisenstein's criterion applied with prime $p$. 

Then by the lemma $f(x)$ is irreducible $\mathbb{Q}[x]$. This completes the proof.
-/

theorem Herstein_exercise_4_5_25 {p : ℕ} (hp : Nat.Prime p) :
  Irreducible (∑ i ∈ Finset.range p, X ^ i : Polynomial ℚ) := by
  classical
  -- Step 1: Upgrade the given proof that `p` is prime to a `Fact` instance so cyclotomic lemmas pick it up.
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  -- Step 2: Identify the geometric sum with the `p`-th cyclotomic polynomial over `ℚ`.
  have hGeom :
      (∑ i ∈ Finset.range p, (X : Polynomial ℚ) ^ i) = Polynomial.cyclotomic p ℚ := by
    -- Step 2.1: Apply the closed form for cyclotomic polynomials when the index is prime.
    simpa using (Polynomial.cyclotomic_prime ℚ p).symm
  -- Step 3: Record the irreducibility of the `p`-th cyclotomic polynomial over `ℚ`.
  have hIrrCyclo : Irreducible (Polynomial.cyclotomic p ℚ) := by
    -- Step 3.1: Use the general lemma once we note that every prime number is positive.
    simpa using (Polynomial.cyclotomic.irreducible_rat (show 0 < p from hp.pos))
  -- Step 4: Transfer the irreducibility statement back to the original polynomial via the identification above.
  -- Step 4.1: Rewrite with `hGeom` so the goals match exactly and conclude.
  simpa [hGeom] using hIrrCyclo
