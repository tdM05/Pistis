import Mathlib
import Mathlib.Tactic.IntervalCases

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

noncomputable section
/-Informal Statement

Prove that $x^4+4x^3+6x^2+2x+1$ is irreducible in $\mathbb{Z}[x]$.
-/

/-Informal Proof

$$
p(x)=x^4+6 x^3+4 x^2+2 x+1
$$
We calculate $p(x-1)$
$$
\begin{aligned}
(x-1)^4 & =x^4-4 x^3+6 x^2-4 x+1 \\
6(x-1)^3 & =6 x^3-18 x^2+18 x-6 \\
4(x-1)^2 & =4 x^2-8 x+4 \\
2(x-1) & =2 x-2 \\
1 & =1
\end{aligned}
$$
$$
\begin{aligned}
& p(x-1)=(x-1)^4+6(x-1)^3+4(x-1)^2+2(x-1)+1=x^4+2 x^3-8 x^2+ \\
& 8 x-2 \\
& q(x)=x^4+2 x^3-8 x^2+8 x-2
\end{aligned}
$$
$q(x)$ is irreducible by Eisenstein's Criterion since the prime $\$ 2 \$$ divides the lower coefficient but $\$ 2^{\wedge} 2 \$$ doesnt divide constant $-2$. Any factorization of $p(x)$ would provide a factor of $p(x)(x-1)$
Since:
$$
\begin{aligned}
& p(x)=a(x) b(x) \\
& q(x)=p(x)(x-1)=a(x-1) b(x-1)
\end{aligned}
$$
We get a contradiction with the irreducibility of $p(x-1)$, so $p(x)$ is irreducible in $Z[x]$
-/

/-!
We prove the irreducibility in three main steps.

1.  Define the auxiliary polynomial
    \[
      g(x) = x^4 - 2x + 2
    \]
    and show that it is irreducible in `ℤ[X]` by Eisenstein's criterion at the
    prime ideal `(2)`.

2.  Observe that `g(x + 1) = x^4 + 4 x^3 + 6 x^2 + 2 x + 1`.  This is expressed
    formally using the algebra automorphism
    `Polynomial.algEquivAevalXAddC (1 : ℤ)`, which sends `p(X)` to `p(X + 1)`.
    Since irreducibility is preserved under multiplicative equivalence, the
    image of an irreducible polynomial under this automorphism is still
    irreducible.

3.  Combine these observations to deduce the irreducibility of the target
    polynomial.
-/

/- Step 0: A small helper lemma describing how `aeval` acts on the constant
   polynomial `2 : ℤ[X]` when the codomain is `ℤ[X]`. -/
lemma aeval_two (x : Polynomial ℤ) :
    aeval x (2 : Polynomial ℤ) = (2 : Polynomial ℤ) := by
  /- Step 0.1: Rewrite `2` as `1 + 1` in the polynomial ring. -/
  have h2 : (2 : Polynomial ℤ) = (1 : Polynomial ℤ) + 1 := by
    -- `norm_num` knows how to evaluate numerals in any semiring.
    norm_num
  /- Step 0.2: Use the algebra-hom properties of `aeval`. -/
  calc
    aeval x (2 : Polynomial ℤ)
        = aeval x ((1 : Polynomial ℤ) + 1) := by
          -- Step 0.2.1: Replace the constant `2` by `1 + 1`.
          simp [h2]
    _ = aeval x (1 : Polynomial ℤ) + aeval x (1 : Polynomial ℤ) := by
          -- Step 0.2.2: `aeval` is additive.
          simp [Polynomial.aeval_add]
    _ = (1 : Polynomial ℤ) + (1 : Polynomial ℤ) := by
          -- Step 0.2.3: `aeval` sends the constant polynomial `1` to `1`.
          simp [Polynomial.aeval_one]
    _ = (2 : Polynomial ℤ) := by
          -- Step 0.2.4: Simplify the sum of two ones.
          norm_num

/- Step 1: Define the Eisenstein polynomial `g(x) = x^4 - 2x + 2`. -/
def g : Polynomial ℤ := X^4 - 2*X + 2

/- Step 2: Show that `g` is irreducible over `ℤ[X]` using Eisenstein's criterion
   at the prime ideal `(2)`. -/
lemma g_irreducible : Irreducible g := by
  -- Step 2.1: Work classically and introduce convenient names.
  classical
  -- Step 2.1.1: Rename `g` to `f` for the argument below.
  set f : Polynomial ℤ := g with hf_def
  -- Step 2.1.2: Let `P = (2)` be the prime ideal that will play the role of
  -- Eisenstein ideal.
  set P : Ideal ℤ := Ideal.span {(2 : ℤ)} with hP_def

  /- Step 2.2: Record that `P` is a prime ideal of `ℤ`. -/
  have hPprime : P.IsPrime := by
    -- Step 2.2.1: View `2` as a prime element in `ℤ`.
    have hPrimeInt : Prime (2 : ℤ) :=
      (Nat.prime_iff_prime_int).1 (by simpa using Nat.prime_two)
    -- Step 2.2.2: Turn the prime element into a prime ideal `(2)`.
    have hTwoNeZero : (2 : ℤ) ≠ 0 := by decide
    simpa [hP_def] using (Ideal.span_singleton_prime hTwoNeZero).2 hPrimeInt

  /- Step 2.3: Split off the lower‑degree tail so that
     `f = X^4 + tail` with `deg tail < 4`. -/
  -- Step 2.3.1: Define the tail part `-2·X + 2`.
  set tail : Polynomial ℤ := (-2 : Polynomial ℤ) * X + Polynomial.C 2 with hTail_def
  -- Step 2.3.2: Expand the definition of `f` explicitly.
  have hf_decomp_raw : f = X^4 - 2*X + 2 := by
    -- `f` is definitionally `g`, and `g` is the polynomial in the statement.
    simp [hf_def, g, sub_eq_add_neg]
  -- Step 2.3.3: Rewrite `f` in the form `X^4 + tail`.
  have hf_decomp : f = X^4 + tail := by
    -- This is a purely algebraic rearrangement.
    simp [hf_decomp_raw, hTail_def, sub_eq_add_neg, add_comm, add_left_comm]

  /- Step 2.4: Show that the degree of `tail` is at most `1`, hence strictly
     smaller than the degree `4` of `X^4`. -/
  -- Step 2.4.1: Bound the degree of the term `(-2)·X`.
  have hTerm_deg_le :
      degree ((-2 : Polynomial ℤ) * X) ≤ (1 : WithBot ℕ) := by
    -- The degree of `C(-2) * X` is exactly `1`.
    have hTwoNeZero : (-2 : ℤ) ≠ 0 := by decide
    have hdeg :
        degree ((-2 : Polynomial ℤ) * X) = (1 : WithBot ℕ) := by
      simpa using
        (Polynomial.degree_C_mul_X (R := ℤ) (a := (-2 : ℤ)) hTwoNeZero)
    exact le_of_eq hdeg
  -- Step 2.4.2: Bound the degree of the constant term.
  have hConst_deg_le :
      degree (2 : Polynomial ℤ) ≤ (0 : WithBot ℕ) := by
    simpa using (Polynomial.degree_C_le (R := ℤ) (a := (2 : ℤ)))
  -- Step 2.4.3: Combine the two bounds to control `degree tail`.
  have hTail_deg_le :
      degree tail ≤ (1 : WithBot ℕ) := by
    have hMax :
        max (degree ((-2 : Polynomial ℤ) * X)) (degree (2 : Polynomial ℤ))
          ≤ (1 : WithBot ℕ) := by
      refine max_le ?_ ?_
      · exact hTerm_deg_le
      ·
        have hZeroLeOne : (0 : WithBot ℕ) ≤ (1 : WithBot ℕ) := by
          exact_mod_cast (Nat.zero_le 1)
        exact hConst_deg_le.trans hZeroLeOne
    have hAdd :=
      Polynomial.degree_add_le ((-2 : Polynomial ℤ) * X) (2 : Polynomial ℤ)
    simpa [tail, hTail_def] using hAdd.trans hMax
  -- Step 2.4.4: Compare this with the known degree of `X^4`.
  have hTail_deg_lt :
      degree tail < degree (X^4 : Polynomial ℤ) := by
    -- The degree of `X^4` is exactly `4`.
    have hXdeg : degree (X^4 : Polynomial ℤ) = (4 : WithBot ℕ) := by
      simp
    -- From `degree tail ≤ 1` and `1 < 4`, we get `deg tail < 4 = deg X^4`.
    have h1lt4 : (1 : WithBot ℕ) < degree (X^4 : Polynomial ℤ) := by
      -- Numerically, `1 < 4`.
      simp [hXdeg]
    exact lt_of_le_of_lt hTail_deg_le h1lt4

  /- Step 2.5: Compute the degree and leading coefficient of `f`. -/
  -- Step 2.5.1: The degree of `f` is the same as the degree of `X^4`, namely `4`.
  have hDegree :
      degree f = (4 : WithBot ℕ) := by
    have :=
      Polynomial.degree_add_eq_left_of_degree_lt
        (p := (X^4 : Polynomial ℤ))
        (q := tail)
        hTail_deg_lt
    simpa [hf_decomp, add_comm] using this
  -- Step 2.5.2: The leading coefficient of `f` is the same as that of `X^4`, i.e. `1`.
  have hfLead :
      f.leadingCoeff = 1 := by
    have hLeadEq :=
      Polynomial.leadingCoeff_add_of_degree_lt'
        (p := (X^4 : Polynomial ℤ))
        (q := tail)
        hTail_deg_lt
    have hLeadEq' :
        f.leadingCoeff = (X^4 : Polynomial ℤ).leadingCoeff := by
      simpa [hf_decomp] using hLeadEq
    have hxLead : ((X^4 : Polynomial ℤ).leadingCoeff) = 1 := by
      simp
    exact hLeadEq'.trans hxLead
  -- Step 2.5.3: Package this as a monic and therefore primitive polynomial.
  have hfMonic : Monic f := by
    -- A polynomial is monic exactly when its leading coefficient is `1`.
    simpa [Polynomial.Monic] using hfLead
  have hfPrim : f.IsPrimitive := hfMonic.isPrimitive

  /- Step 2.6: The leading coefficient is not in `P` (since `1 ∉ (2)`). -/
  have hOneNot : (1 : ℤ) ∉ P :=
    (Ideal.ne_top_iff_one _).1 hPprime.ne_top
  have hLeadNot : f.leadingCoeff ∉ P := by
    simpa [hfLead] using hOneNot

  /- Step 2.7: Every lower coefficient of `f` lies in the ideal `(2)`. -/
  have hCoeffs :
      ∀ m : ℕ, (m : WithBot ℕ) < degree f → f.coeff m ∈ P := by
    intro m hm
    -- Step 2.7.1: Convert the bound on `(m : WithBot ℕ)` into a bound on `m : ℕ`.
    have hmLt : m < 4 := by
      have := (by simpa [hDegree] using hm :
        (m : WithBot ℕ) < (4 : WithBot ℕ))
      exact_mod_cast this
    -- Step 2.7.2: Exhaust possibilities for `m = 0,1,2,3`.
    interval_cases m
    · -- Case `m = 0`: constant term `2` is divisible by `2`.
      have hCoeff0 : f.coeff 0 = 2 := by
        simp [hf_decomp_raw]
      have hMul : (2 : ℤ) ∣ (2 : ℤ) := ⟨1, by norm_num⟩
      have hMem : (2 : ℤ) ∈ P := by
        simpa [hP_def] using (Ideal.mem_span_singleton).2 hMul
      simpa [hCoeff0]
    · -- Case `m = 1`: coefficient `-2` is also divisible by `2`.
      have hCoeff1 : f.coeff 1 = -2 := by
        simp [hf_decomp_raw]
      have hMul : (2 : ℤ) ∣ (-2 : ℤ) := ⟨-1, by norm_num⟩
      have hMem : (-2 : ℤ) ∈ P := by
        simpa [hP_def] using (Ideal.mem_span_singleton).2 hMul
      -- Rewrite the goal using the explicit coefficient computation.
      -- After replacing `f.coeff 1` by `-2`, the statement follows from `hMem`.
      simpa [hCoeff1] using hMem
    · -- Case `m = 2`: the coefficient is `0`, which lies in every ideal.
      have hCoeff2 : f.coeff 2 = 0 := by
        -- First compute the coefficient of `X` at degree `2`.
        have hXcoeff2 : (X : Polynomial ℤ).coeff 2 = 0 := by
          simpa using
            (Polynomial.coeff_X_pow (R := ℤ) (k := 1) (n := 2))
        -- Then expand the definition of `f`.
        simp [hf_decomp_raw, sub_eq_add_neg, hXcoeff2]
      -- Replace `f.coeff 2` by `0` and conclude using `Ideal.zero_mem`.
      simp [hCoeff2]
    · -- Case `m = 3`: the coefficient is again `0`.
      have hCoeff3 : f.coeff 3 = 0 := by
        -- As above, use the general formula for coefficients of powers of `X`.
        have hXcoeff3 : (X : Polynomial ℤ).coeff 3 = 0 := by
          simpa using
            (Polynomial.coeff_X_pow (R := ℤ) (k := 1) (n := 3))
        simp [hf_decomp_raw, sub_eq_add_neg, hXcoeff3]
      simp [hCoeff3]

  /- Step 2.8: The polynomial `f` has strictly positive degree (`deg f = 4`). -/
  have hDegPos : 0 < degree f := by
    have : (0 : WithBot ℕ) < (4 : WithBot ℕ) := by
      exact_mod_cast (Nat.succ_pos 3)
    simp [hDegree]

  /- Step 2.9: Show that the constant coefficient is *not* in `(2)^2`, i.e.,
     `4 ∤ 2`. -/
  have hfCoeff0 : f.coeff 0 = 2 := by
    simp [hf_decomp_raw]
  have hConstNot : f.coeff 0 ∉ P ^ 2 := by
    -- Step 2.9.1: Reformulate membership in `P^2` as divisibility by `2^2 = 4`.
    intro hMem
    obtain ⟨k, hk⟩ :=
      (Ideal.mem_span_singleton).1
        (by
          simpa [hP_def, Ideal.span_singleton_pow, hfCoeff0] using hMem)
    -- Step 2.9.2: Move from integer‑valued divisibility to natural numbers.
    have hNatDiv : (4 : ℕ) ∣ 2 := by
      have hAbs := congrArg Int.natAbs hk
      have hPow : Int.natAbs ((2 : ℤ) ^ 2) = (4 : ℕ) := by
        simp [pow_two]
      refine ⟨Int.natAbs k, ?_⟩
      simpa [Int.natAbs_mul, Int.natAbs_natCast, hPow] using hAbs
    -- Step 2.9.3: But `4 ∤ 2`, contradiction.
    have hNot : ¬ (4 : ℕ) ∣ 2 := by decide
    exact hNot hNatDiv

  /- Step 2.10: Apply Eisenstein's criterion to conclude irreducibility of `f`. -/
  have hIrred :
      Irreducible f :=
    Polynomial.irreducible_of_eisenstein_criterion
      (f := f)
      (P := P)
      hPprime
      hLeadNot
      hCoeffs
      hDegPos
      hConstNot
      hfPrim

  /- Step 2.11: Undo the abbreviation `f = g`. -/
  simpa [hf_def, g] using hIrred

/- Step 3: Relate `g` to the target polynomial via the shift `X ↦ X + 1`. -/
lemma g_shifted :
    aeval (X + 1 : Polynomial ℤ) g
      = (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  /- Step 3.1: Compute `aeval (X + 1)` on `g`. -/
  -- Step 3.1.1: Evaluation of the indeterminate.
  have hx :
      aeval (X + 1 : Polynomial ℤ) (X : Polynomial ℤ)
        = (X + 1 : Polynomial ℤ) := by
    simp [Polynomial.aeval_X]
  -- Step 3.1.2: Use the algebra hom properties of `aeval` together with the
  -- helper lemma `aeval_two` to expand the expression.
  have h1 :
      aeval (X + 1 : Polynomial ℤ) g
        = (X + 1)^4 - 2*(X + 1) + 2 := by
    -- The `simp` call expands powers and products and evaluates the small
    -- integer coefficients via `aeval_two`.
    simp [g, sub_eq_add_neg, Polynomial.aeval_add, Polynomial.aeval_mul,
      Polynomial.aeval_X_pow, hx, aeval_two]
  /- Step 3.2.3: Expand `(X + 1)^4 - 2·(X + 1) + 2` and compare with the
     polynomial from the statement. -/
  have h2 :
      (X + 1)^4 - 2*(X + 1) + 2
        = (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
    ring
  /- Step 3.2: Combine the equalities. -/
  calc
    aeval (X + 1 : Polynomial ℤ) g
        = (X + 1)^4 - 2*(X + 1) + 2 := h1
    _ = (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := h2

/- Step 4: Conclude irreducibility of the target polynomial from the
   irreducibility of `g` and the fact that the shift is a multiplicative
   equivalence. -/
theorem Dummit_Foote_exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  -- Step 4.1: `algEquivAevalXAddC (1 : ℤ)` is an algebra (and hence multiplicative)
  -- equivalence on `ℤ[X]`. Irreducibility is preserved under such equivalences.
  have h_g :
      Irreducible ((Polynomial.algEquivAevalXAddC (1 : ℤ)) g) :=
    -- `Irreducible.map` sends irreducible elements through multiplicative
    -- equivalences.
    Irreducible.map (f := Polynomial.algEquivAevalXAddC (1 : ℤ)) g_irreducible
  -- Step 4.2: Identify the image of `g` under the automorphism with
  -- evaluation at `X + 1`.
  have h_iso :
      (Polynomial.algEquivAevalXAddC (1 : ℤ)) g
        = aeval (X + 1 : Polynomial ℤ) g := by
    simp [Polynomial.algEquivAevalXAddC, g]
  have h_g' :
      Irreducible (aeval (X + 1 : Polynomial ℤ) g) := by
    simpa [h_iso] using h_g
  -- Step 4.3: Rewrite again using the explicit expansion `g_shifted`.
  simpa [g_shifted] using h_g'
