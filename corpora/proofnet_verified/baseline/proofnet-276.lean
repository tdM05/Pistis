import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $a \in K$ is such that $a^2$ is algebraic over the subfield $F$ of $K$, show that a is algebraic over $F$.
-/

/-Informal Proof

Since $a^2$ is algebraic over $F$, there exist a non-zero polynomial $f(x)$ in $F[x]$ such that $f\left(a^2\right)=0$. Consider a new polynomial $g(x)$ defined as $g(x)=f\left(x^2\right)$. Clearly $g(x) \in F[x]$ and $g(a)=f\left(a^2\right)= 0$.
-/

theorem Herstein_exercise_5_3_7 {K : Type*} [Field K] {F : Subfield K}
  {a : K} (ha : IsAlgebraic F (a ^ 2)) : IsAlgebraic F a := by
  classical
  
  -- Step 1: Expand the hypothesis `ha : IsAlgebraic F (a ^ 2)`.
  --`IsAlgebraic F x` means there is a non-zero polynomial `p : Polynomial F`
  --with coefficients in the base field `F` such that `aeval x p = 0`.
  rcases ha with ⟨p, hp_nonzero, hp_root⟩

  -- Step 2: Define the auxiliary polynomial `q(X) = p(X^2)`.
  --This lives in the same coefficient field `F` and will satisfy `q a = 0`.
  let q : Polynomial F := p.comp (Polynomial.X ^ (2 : ℕ))

  -- Step 3: Prove that `q` is *not* the zero polynomial.
  --We show that its leading coefficient is non-zero by relating it to that of `p`.
  have hq_nonzero : q ≠ 0 := by
    -- Step 3.1: record the degree of the inner polynomial `X^2` is not zero.
    -- This is needed by the lemma `leadingCoeff_comp`.
    have hdeg_inner : Polynomial.natDegree (Polynomial.X ^ (2 : ℕ) : Polynomial F) ≠ 0 := by
      -- `natDegree (X^2)` is `2`, which is obviously non-zero.
      -- We spell it out for clarity.
      have : (Polynomial.natDegree (Polynomial.X ^ (2 : ℕ) : Polynomial F)) = 2 := by
        -- Step 3.1.1: the degree of a power of `X` is the exponent itself.
        -- `simp` knows `natDegree_X_pow` and evaluates directly.
        simp
      -- Step 3.1.2: Convert the explicit value into the desired non-vanishing statement.
      simp [this]

    -- Step 3.2: compute the leading coefficient of `q = p.comp (X^2)` using `leadingCoeff_comp`.
    -- Because `X^2` is monic, the leading coefficient of the composition equals that of `p`.
    have hlead_q : q.leadingCoeff = p.leadingCoeff := by
      -- unfold `q` and simplify the formula delivered by `leadingCoeff_comp`.
      unfold q
      -- `leadingCoeff (X^2)` is `1`, so the multiplicative factor becomes `1 ^ deg p = 1`.
      -- The hypothesis `hdeg_inner` supplies the needed degree non-vanishing.
      simpa using
        (Polynomial.leadingCoeff_comp (p := p)
            (q := (Polynomial.X ^ (2 : ℕ) : Polynomial F)) hdeg_inner)

    -- Step 3.3: the leading coefficient of `p` is non-zero because `p ≠ 0`.
    have hlead_p : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp_nonzero

    -- Step 3.4: conclude that `q` itself cannot be the zero polynomial.
    -- If it were zero, its leading coefficient would be zero; this contradicts the equality above.
    intro hq_zero
    have hlead_q_zero : q.leadingCoeff = 0 := by simp [hq_zero]
    exact hlead_p (hlead_q_zero ▸ hlead_q.symm)

  -- Step 4: Show that `a` is a root of `q`.
  -- This is immediate from `hp_root : aeval (a^2) p = 0` and the construction of `q`.
  have hq_root : Polynomial.aeval a q = 0 := by
    -- Compute `aeval` of the composition explicitly.
    -- Using `aeval_comp_apply` gives `aeval a (p.comp r) = aeval (aeval a r) p`.
    -- Here `r = X^2`, and `aeval a (X^2)` reduces to `a^2` by the algebra homomorphism laws.
    -- Step 4.1: replace `q` by its definition inside the goal.
    change Polynomial.aeval a (p.comp (Polynomial.X ^ (2 : ℕ) : Polynomial F)) = 0

    -- Step 4.2: use the standard composition lemma for `aeval`.
    calc
      Polynomial.aeval a (p.comp (Polynomial.X ^ (2 : ℕ) : Polynomial F))
          = Polynomial.aeval (Polynomial.aeval a (Polynomial.X ^ (2 : ℕ) : Polynomial F)) p := by
              exact (Polynomial.aeval_comp (p := p)
                (q := (Polynomial.X ^ (2 : ℕ) : Polynomial F)) (x := a))
      _ = Polynomial.aeval (a ^ 2) p := by
              -- Step 4.3: simplify the inner evaluation `(aeval a (X^2))` to `a^2`.
              simp
      _ = 0 := hp_root

  -- Step 5: Package everything: `q` is a non-zero polynomial over `F` with `aeval a q = 0`.
  -- This is exactly the definition of `IsAlgebraic F a`.
  exact ⟨q, hq_nonzero, hq_root⟩
