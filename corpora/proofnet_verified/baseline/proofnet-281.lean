import Mathlib

open Real
open scoped BigOperators



/-Informal Statement

Show that $\sum^{\prime} 1 / n$, the sum being over square free integers, diverges.
-/

/-Informal Proof

Let $S \subset \mathbb{N}^*$ the set of square free integers.

Let $N \in \mathbb{N}^*$. Every integer $n, \, 1\leq n \leq N$ can be written as $n = a b^2$, where $a,b$ are integers and $a$ is square free. Then $1\leq a \leq N$, and $1\leq b \leq \sqrt{N}$, so
$$\sum_{n\leq N} \frac{1}{n} \leq \sum_{a \in S, a\leq N}\  \sum_{1\leq b \leq \sqrt{N}} \frac{1}{ab^2} \leq  \sum_{a \in S, a\leq N}\ \frac{1}{a} \, \sum_{b=1}^\infty  \frac{1}{b^2} = \frac{\pi^2}{6} \sum_{a \in S, a\leq N}\ \frac{1}{a}.$$
So $$\sum_{a \in S, a\leq N} \frac{1}{a}  \geq \frac{6}{\pi^2} \sum_{n\leq N} \frac{1}{n}.$$
As $\sum_{n=1}^\infty \frac{1}{n}$ diverges, $\lim\limits_{N \to \infty} \sum\limits_{a \in S, a\leq N} \frac{1}{a} = +\infty$, so the family $\left(\frac{1}{a}\right)_{a\in S}$ of the inverse of square free integers is not summable.

Let $S_N = \prod_{p<N}(1+1/p)$ , and $p_1,p_2,\ldots, p_l\ (l = l(N))$ all prime integers less than $N$. Then
\begin{align*}
S_N &= \left(1+\frac{1}{p_1}\right) \cdots \left(1+\frac{1}{p_l}\right)\\
&=\sum_{(\varepsilon_1,\cdots,\varepsilon_l) \in \{0,1\}^l } \frac{1}{p_1^{\varepsilon_1} \cdots p_l^{\varepsilon_l}}
\end{align*}
We prove this last formula  by induction. This is true for $l=1$ : $\sum_{\varepsilon \in \{0,1\}} 1/p_1^\varepsilon = 1 + 1/p_1$.

If it is true for the integer $l$, then 
\begin{align*}
\left(1+\frac{1}{p_1}\right) \cdots \left(1+\frac{1}{p_l}\right)\left(1+\frac{1}{p_{l+1}}\right) &= \sum_{(\varepsilon_1,\ldots,\varepsilon_l) \in \{0,1\}^l } \frac{1}{p_1^{\varepsilon_1} \cdots p_l^{\varepsilon_l}} \left(1+\frac{1}{p_{l+1}}\right)\\
&=\sum_{(\varepsilon_1,\ldots,\varepsilon_l) \in \{0,1\}^l } \frac{1}{p_1^{\varepsilon_1} \cdots p_l^{\varepsilon_l}} + \sum_{(\varepsilon_1,\ldots,\varepsilon_l) \in \{0,1\}^l } \frac{1}{p_1^{\varepsilon_1} \cdots p_l^{\varepsilon_l}p_{l+1}}\\
&=\sum_{(\varepsilon_1,\ldots,\varepsilon_l,\varepsilon_{l+1}) \in \{0,1\}^{l+1} } \frac{1}{p_1^{\varepsilon_1} \cdots p_l^{\varepsilon_l}p_{l+1}^{\varepsilon_{l+1}}} 
\end{align*}
So it is true for all $l$. 

Thus $S_N = \sum_{n\in \Delta} \frac{1}{n}$, where $\Delta$ is the set of square free integers whose prime factors are less than $N$.

As $\sum 1/n$, the sum being over square free integers, diverges, $\lim\limits_{N\to \infty} S_N = + \infty$ :
$$\lim_{N \to \infty} \prod_{p<N} \left(1+\frac{1}{p}\right) = +\infty.$$
 $e^x \geq 1+x, x \geq \log (1+x)$ for $x>0$, so
$$\log S_N = \sum_{k=1}^{l(N)} \log\left(1+\frac{1}{p_k}\right) \leq \sum_{k=1}^{l(N)} \frac{1}{p_k}.$$
$\lim\limits_{N\to \infty} \log S_N = +\infty$ and $\lim\limits_{N\to \infty} l(N) = +\infty$, so
$$\lim_{N\to \infty} \sum_{p<N} \frac{1}{p} = +\infty.$$
-/

theorem Ireland_Rosen_exercise_2_27a :
  ¬ Summable (λ i : {p : ℤ // Squarefree p} => (1 : ℚ) / i) := by
  classical
  /- Step 1: argue by contradiction, so assume the series over squarefree integers converges. -/
  intro h

  /- Step 2: move the series to ℝ via the continuous inclusion `ℚ ↪ ℝ` so we can use
     completeness arguments later. -/
  let ratToReal : ℚ →+ ℝ :=
    { toFun := fun q => (q : ℝ)
      map_zero' := by simp
      map_add' := by intro a b; simp }
  /- Step 2.1: applying this inclusion to the whole series preserves summability. -/
  have h_real_cast :
      Summable (fun i : {p : ℤ // Squarefree p} => ratToReal ((1 : ℚ) / (i : ℤ))) :=
    h.map ratToReal Rat.continuous_coe_real
  /- Step 2.2: rewrite those terms explicitly as real reciprocals. -/
  have h_real : Summable (fun i : {p : ℤ // Squarefree p} => (1 : ℝ) / ((i : ℤ) : ℝ)) := by
    refine h_real_cast.congr ?_
    intro i
    simp [ratToReal]

  /- Step 3: embed primes into the squarefree integers so that we can pull back the series. -/
  let primeEmbedding : Nat.Primes → {p : ℤ // Squarefree p} := fun p =>
    ⟨(p : ℤ), by
      /- Step 3.1: every prime natural number is squarefree. -/
      have hNat : Squarefree (p : ℕ) := by
        simpa using (p.property.squarefree : Squarefree (p : ℕ))
      /- Step 3.2: shuttle this fact to the integer `p` using `Int.squarefree_natCast`. -/
      exact (Int.squarefree_natCast (n := p)).2 hNat⟩

  /- Step 4: verify that the embedding above is injective. -/
  have primeEmbedding_inj : Function.Injective primeEmbedding := by
    intro p q hpq
    /- Step 4.1: equal images give an equality of the underlying integers. -/
    have hvals : (p : ℤ) = (q : ℤ) := congrArg Subtype.val hpq
    /- Step 4.2: the inclusion `ℕ → ℤ` is injective, so we get equality back in `ℕ`. -/
    have hnat : (p : ℕ) = q := by
      apply Int.ofNat.inj
      simpa using hvals
    /- Step 4.3: conclude by extensionality of the subtype `Nat.Primes`. -/
    apply Subtype.ext
    simpa using hnat

  /- Step 5: restrict the real-valued series along the embedding to get a sum over primes. -/
  have h_primes_real_raw :
      Summable
        (fun p : Nat.Primes =>
          (1 : ℝ) / (((primeEmbedding p : {p : ℤ // Squarefree p}) : ℤ) : ℝ)) :=
    h_real.comp_injective primeEmbedding_inj
  have h_primes_real : Summable (fun p : Nat.Primes => (1 : ℝ) / (p : ℝ)) := by
    /- Step 5.1: the terms simplify because the embedding remembers exactly the prime. -/
    simpa [primeEmbedding] using h_primes_real_raw

  /- Step 6: contradict the known divergence of the sum of reciprocals of the primes. -/
  exact Nat.Primes.not_summable_one_div h_primes_real
