import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

set_option maxRecDepth 10000



/-!
In this file we work with the finite field `ZMod 7` and the polynomials
`X^3 - 2` and `X^3 + 2`.  We first establish that no element of `ZMod 7`
has cube equal to `2` or `-2`, and then prove a general irreducibility
lemma for degree–3 polynomials over a field with no roots.  Finally we
apply these facts to show that the two given cubics are irreducible and
that the corresponding quotient fields are isomorphic.
-/

lemma no_cube_eq_two_ZMod7 (y : ZMod 7) : y ^ 3 ≠ (2 : ZMod 7) := by
  -- Step 1: Assume, for contradiction, that `y ^ 3 = 2` in `ZMod 7`.
  intro h
  -- Step 2: Show that `y` is nonzero, since otherwise its cube would be `0`, not `2`.
  have hy_nonzero : (y : ZMod 7) ≠ 0 := by
    -- Step 2.1: Suppose `y = 0` and derive an impossible equality `0 = 2`.
    intro hy
    -- Step 2.2: Rewrite the assumed cube equation using `y = 0`.
    have h0 : (0 : ZMod 7) = (2 : ZMod 7) := by
      -- `y ^ 3 = 2` becomes `0 ^ 3 = 2`, i.e. `0 = 2`.
      have : (0 : ZMod 7) ^ 3 = (2 : ZMod 7) := by simpa [hy] using h
      simpa using this
    -- Step 2.3: Eliminate the impossible equality `0 = 2` in `ZMod 7`.
    exact (by decide : (0 : ZMod 7) ≠ (2 : ZMod 7)) h0
  -- Step 3: Square both sides of `y ^ 3 = 2` to obtain an equation for `y ^ 6`.
  have hpow6 : (y : ZMod 7) ^ 6 = (4 : ZMod 7) := by
    -- Step 3.1: Apply the squaring map to both sides of the cube equation.
    have hsq := congrArg (fun t : ZMod 7 => t ^ 2) h
    -- Step 3.2: Simplify the left-hand side to `y ^ 6` and the right-hand side to `4`.
    -- `(y ^ 3) ^ 2 = y ^ 6` and `2 ^ 2 = 4`.
    have hsq' : (y : ZMod 7) ^ 6 = (4 : ZMod 7) := by
      -- First rewrite `(y ^ 3) ^ 2` as `y ^ 6`.
      have h6 : (6 : ℕ) = 3 * 2 := by decide
      calc
        (y : ZMod 7) ^ 6
            = (y : ZMod 7) ^ (3 * 2) := by simp [h6]
        _ = ((y : ZMod 7) ^ 3) ^ 2 := by
          simpa using (pow_mul (y : ZMod 7) 3 2)
        _ = (4 : ZMod 7) := by simpa [pow_two] using hsq
    -- Step 3.3: Record the simplified sixth-power equation.
    exact hsq'
  -- Step 4: Use Fermat's Little Theorem to compute `y ^ 6` in another way.
  have hfermat : (y : ZMod 7) ^ 6 = (1 : ZMod 7) := by
    -- Step 4.1: Register the primality of `7` so we can apply the standard lemma.
    haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
    -- Step 4.2: Apply Fermat's Little Theorem in `ZMod 7`.
    simpa using (ZMod.pow_card_sub_one_eq_one (p := 7) (a := (y : ZMod 7)) hy_nonzero)
  -- Step 5: Combine the two expressions for `y ^ 6` to deduce `1 = 4`, a contradiction.
  have h_one_eq_four : (1 : ZMod 7) = (4 : ZMod 7) := by
    -- Step 5.1: Rewrite `y ^ 6` as `1` using Fermat's theorem.
    simpa [hfermat] using hpow6
  -- Step 6: Eliminate the impossible equality `1 = 4` to conclude the proof.
  exact (by decide : (1 : ZMod 7) ≠ (4 : ZMod 7)) h_one_eq_four

lemma no_cube_eq_neg_two_ZMod7 (y : ZMod 7) : y ^ 3 ≠ (-2 : ZMod 7) := by
  -- Step 1: Assume, for contradiction, that `y ^ 3 = -2` in `ZMod 7`.
  intro h
  -- Step 2: Consider the element `-y` and compute its cube.
  have hneg_cube : (-y : ZMod 7) ^ 3 = (2 : ZMod 7) := by
    -- Step 2.1: First rewrite `(-y) ^ 3` as `- y ^ 3` using basic ring identities.
    have hpow : (-y : ZMod 7) ^ 3 = - (y : ZMod 7) ^ 3 := by
      -- Expand the cube and simplify:
      -- `(-y)^3 = (-y) * (-y) * (-y) = -(y * y * y) = -y^3`.
      simp [pow_succ, mul_comm]
    -- Step 2.2: Use the assumed equality `y ^ 3 = -2` to rewrite the right-hand side.
    have hneg : - (y : ZMod 7) ^ 3 = (2 : ZMod 7) := by
      -- Negating both sides of `y ^ 3 = -2` yields `- y^3 = 2`.
      have := congrArg Neg.neg h
      simpa using this
    -- Step 2.3: Combine the two equalities to obtain `(-y) ^ 3 = 2`.
    exact hpow.trans hneg
  -- Step 3: Invoke the previous lemma, which forbids any cube equal to `2`.
  have hcontr := no_cube_eq_two_ZMod7 (-y)
  -- Step 4: Derive the final contradiction.
  exact hcontr hneg_cube

/-!
We now set up a convenient description of the polynomial ring `ZMod 7[X]`
and of the substitution automorphism sending `X` to `-X`.  These
definitions will be used later to relate the quotient rings defined by
the polynomials `X^3 - 2` and `X^3 + 2`.
-/

-- Step A: A short name for the polynomial ring `ZMod 7[X]`.
abbrev ZMod7Poly := Polynomial (ZMod 7)

-- Step B: The ring homomorphism corresponding to the substitution `X ↦ -X`.
noncomputable def negXSubst : ZMod7Poly →+* ZMod7Poly :=
  Polynomial.compRingHom (-X : ZMod7Poly)

-- Step C: An explicit formula for `negXSubst` on each polynomial.
lemma negXSubst_apply (f : ZMod7Poly) :
    negXSubst f = f.comp (-X) := by
  -- Step C.1: Identify the underlying function of `negXSubst` using
  -- `Polynomial.coe_compRingHom`, which says that `q.compRingHom`
  -- acts by composition with `q`.
  have hfun :
      (fun p : ZMod7Poly => negXSubst p) =
        fun p : ZMod7Poly => p.comp (-X) := by
    simp [negXSubst, Polynomial.coe_compRingHom]
  -- Step C.2: Apply this function equality to the specific polynomial `f`.
  have := congrArg (fun g : ZMod7Poly → ZMod7Poly => g f) hfun
  simpa using this

-- Step D: The substitution `X ↦ -X` is an involution on `ZMod 7[X]`.
lemma negXSubst_involutive :
    Function.Involutive (fun f : ZMod7Poly => negXSubst f) := by
  -- Step D.1: Fix an arbitrary polynomial `f`.
  intro f
  -- Step D.2: Use the explicit formula for `negXSubst` twice.
  have h1 :
      negXSubst (negXSubst f) = (negXSubst f).comp (-X) :=
    negXSubst_apply (negXSubst f)
  have h2 :
      negXSubst f = f.comp (-X) :=
    negXSubst_apply f
  -- Step D.3: Reduce the problem to analysing `(f.comp (-X)).comp (-X)`.
  have hassoc :
      (f.comp (-X)).comp (-X) =
        f.comp ((-X : ZMod7Poly).comp (-X)) := by
    simp [Polynomial.comp_assoc]
  -- Step D.4: Compute `(-X).comp (-X) = X`.
  have hneg :
      (-X : ZMod7Poly).comp (-X) = (X : ZMod7Poly) := by
    simp
  -- Step D.5: Simplify `(f.comp (-X)).comp (-X)` to `f.comp X`.
  have hcompX :
      (f.comp (-X)).comp (-X) = f.comp X := by
    simpa [hneg] using hassoc
  -- Step D.6: Finally, `f.comp X = f` for all polynomials.
  have hcompId : f.comp X = f := by
    simp [Polynomial.comp_X]
  -- Step D.7: Chain all equalities together.
  calc
    negXSubst (negXSubst f)
        = (negXSubst f).comp (-X) := h1
    _ = (f.comp (-X)).comp (-X) := by simp [h2]
    _ = f.comp X := hcompX
    _ = f := hcompId

namespace Polynomial

lemma irreducible_of_degree_three_of_no_root
  {K : Type*} [Field K] {p : Polynomial K}
  (hdeg : p.degree = 3)
  (hroot : ∀ x : K, ¬ p.IsRoot x) :
  Irreducible p := by
  classical
  -- Step 1: Prove that `p` is nonzero from the degree information.
  have hp_ne_zero : p ≠ 0 := by
    -- If `p = 0`, then its degree is `⊥`, contradicting `degree p = 3`.
    intro hzero
    simp [hzero] at hdeg
  -- Step 2: Show that `p` cannot be a unit because its degree is not zero.
  have hp_not_unit : ¬ IsUnit p := by
    -- Step 2.1: If `p` were a unit, its degree would be zero.
    intro hp_unit
    have hdeg0 : p.degree = 0 :=
      (Polynomial.isUnit_iff_degree_eq_zero (p := p)).mp hp_unit
    -- Step 2.2: Combine `degree p = 0` with `degree p = 3`.
    have hzero_three : (0 : WithBot ℕ) = 3 := by
      calc
        (0 : WithBot ℕ) = p.degree := by simp [hdeg0]
        _ = 3 := hdeg
    -- Step 2.3: Eliminate the impossible equality `0 = 3`.
    exact (by decide : (0 : WithBot ℕ) ≠ (3 : WithBot ℕ)) hzero_three
  -- Step 3: Convert the degree statement to a statement about `natDegree`.
  have hdegNat : p.natDegree = 3 := by
    -- Step 3.1: For nonzero polynomials, `degree p = n` is equivalent to `natDegree p = n`.
    have hiff := (Polynomial.degree_eq_iff_natDegree_eq (p := p) (hp := hp_ne_zero) (n := 3))
    -- Step 3.2: Extract the `natDegree` equality using the given `degree` equality.
    exact (hiff.mp hdeg)
  -- Step 4: Prepare to use the definition of irreducibility.
  refine ⟨hp_not_unit, ?_⟩
  -- Step 5: Consider an arbitrary factorization `p = a * b`.
  intro a b hFactor
  -- Step 5.1: If `a` is a unit, we are already done.
  by_cases ha_unit : IsUnit a
  · exact Or.inl ha_unit
  -- Step 5.2: If `b` is a unit, we are done as well.
  · by_cases hb_unit : IsUnit b
    · exact Or.inr hb_unit
    -- Step 5.3: Now suppose *both* `a` and `b` are nonunits; we derive a contradiction.
    · have ha_nonunit : ¬ IsUnit a := ha_unit
      have hb_nonunit : ¬ IsUnit b := hb_unit
      -- Step 5.3.1: Show that `a` and `b` are nonzero, otherwise `p` would be zero.
      have ha_ne_zero : a ≠ 0 := by
        intro hzero
        have : p = 0 := by
          -- If `a = 0`, then `p = a * b = 0 * b = 0`.
          simp [hFactor, hzero]
        exact hp_ne_zero this
      have hb_ne_zero : b ≠ 0 := by
        intro hzero
        have : p = 0 := by
          -- If `b = 0`, then `p = a * b = a * 0 = 0`.
          simp [hFactor, hzero]
        exact hp_ne_zero this
      -- Step 5.3.2: Convert nonunit information into strict positivity of the degrees.
      have hdeg_a_pos : 0 < degree a :=
        Polynomial.degree_pos_of_ne_zero_of_nonunit ha_ne_zero ha_nonunit
      have hdeg_b_pos : 0 < degree b :=
        Polynomial.degree_pos_of_ne_zero_of_nonunit hb_ne_zero hb_nonunit
      -- Step 5.3.3: Translate these degree inequalities to `natDegree` inequalities.
      have hnat_a_pos : 0 < a.natDegree :=
        (Polynomial.natDegree_pos_iff_degree_pos (p := a)).2 hdeg_a_pos
      have hnat_b_pos : 0 < b.natDegree :=
        (Polynomial.natDegree_pos_iff_degree_pos (p := b)).2 hdeg_b_pos
      -- Step 5.3.4: Record the equality of `natDegree`s coming from `p = a * b`.
      have hsumNat : a.natDegree + b.natDegree = p.natDegree := by
        -- The degree of a nonzero product is the sum of the degrees of the factors.
        have hmul :
            (a * b : Polynomial K).natDegree = a.natDegree + b.natDegree :=
          Polynomial.natDegree_mul (p := a) (q := b) ha_ne_zero hb_ne_zero
        -- Use `p = a * b` to rewrite the left-hand side.
        simpa [hFactor] using hmul.symm
      -- Step 5.3.5: Make explicit that `a.natDegree + b.natDegree = 3`.
      have hsum : a.natDegree + b.natDegree = 3 := by
        simpa [hdegNat] using hsumNat
      -- Step 5.3.6: Case split on whether `a` has `natDegree ≤ 1` or not.
      by_cases h_a_le_one : a.natDegree ≤ 1
      · -- Step 5.3.6.1: In this subcase, `natDegree a` is both ≥ 1 and ≤ 1, hence equals 1.
        have h_a_ge_one : 1 ≤ a.natDegree := Nat.succ_le_of_lt hnat_a_pos
        have h_a_nat_one : a.natDegree = 1 :=
          le_antisymm h_a_le_one h_a_ge_one
        -- Step 5.3.6.2: Translate `natDegree a = 1` into `degree a = 1`.
        have h_deg_a_one : a.degree = 1 := by
          have hiff :=
            (Polynomial.degree_eq_iff_natDegree_eq (p := a)
              (hp := ha_ne_zero) (n := 1))
          exact (hiff.mpr h_a_nat_one)
        -- Step 5.3.6.3: Use the degree-1 lemma to produce a root of `a`.
        obtain ⟨x, hx_root_a⟩ :=
          Polynomial.exists_root_of_degree_eq_one (p := a) h_deg_a_one
        -- Step 5.3.6.4: Turn a root of `a` into a root of `p = a * b`.
        have hx_eval_a_zero : a.eval x = 0 := by
          simpa [Polynomial.IsRoot] using hx_root_a
        have hx_eval_p_zero : p.eval x = 0 := by
          calc
            p.eval x = (a * b).eval x := by simp [hFactor]
            _ = a.eval x * b.eval x := by
              simp [Polynomial.eval_mul]
            _ = 0 := by simp [hx_eval_a_zero]
        have hx_root_p : p.IsRoot x := by
          simpa [Polynomial.IsRoot] using hx_eval_p_zero
        -- Step 5.3.6.5: Contradict the assumption that `p` has no roots.
        have hFalse : False := hroot x hx_root_p
        exact hFalse.elim
      · -- Step 5.3.6.6: In the complementary subcase, `a.natDegree ≥ 2`.
        have h_a_ge_two : 2 ≤ a.natDegree := by
          -- From `¬ a.natDegree ≤ 1` we deduce `1 < a.natDegree`, hence `2 ≤ a.natDegree`.
          have h_lt : 1 < a.natDegree := Nat.lt_of_not_ge h_a_le_one
          exact Nat.succ_le_of_lt h_lt
        -- Step 5.3.6.7: Use the equality `a.natDegree + b.natDegree = 3` to bound `b.natDegree`.
        have h_b_le_one : b.natDegree ≤ 1 := by
          -- From `2 ≤ a.natDegree` we get `2 + b.natDegree ≤ a.natDegree + b.natDegree = 3`.
          have h2 : 2 + b.natDegree ≤ a.natDegree + b.natDegree :=
            Nat.add_le_add_right h_a_ge_two _
          -- Replace `a.natDegree + b.natDegree` by `3` using `hsum`.
          have h2' : 2 + b.natDegree ≤ 3 := by
            simpa [hsum] using h2
          -- Rewrite `3` as `2 + 1` to use `Nat.add_le_add_iff_left`.
          have h2'' : 2 + b.natDegree ≤ 2 + 1 := by
            simpa [Nat.succ_eq_add_one] using h2'
          -- Finally cancel `2` from both sides to obtain `b.natDegree ≤ 1`.
          exact Nat.le_of_add_le_add_left h2''
        -- Step 5.3.6.8: Combine `0 < b.natDegree` and `b.natDegree ≤ 1` to get `b.natDegree = 1`.
        have h_b_ge_one : 1 ≤ b.natDegree := Nat.succ_le_of_lt hnat_b_pos
        have h_b_nat_one : b.natDegree = 1 :=
          le_antisymm h_b_le_one h_b_ge_one
        -- Step 5.3.6.9: Translate `natDegree b = 1` into `degree b = 1`.
        have h_deg_b_one : b.degree = 1 := by
          have hiff :=
            (Polynomial.degree_eq_iff_natDegree_eq (p := b)
              (hp := hb_ne_zero) (n := 1))
          exact (hiff.mpr h_b_nat_one)
        -- Step 5.3.6.10: Use the degree-1 lemma to produce a root of `b`.
        obtain ⟨x, hx_root_b⟩ :=
          Polynomial.exists_root_of_degree_eq_one (p := b) h_deg_b_one
        -- Step 5.3.6.11: Turn this into a root of `p = a * b`.
        have hx_eval_b_zero : b.eval x = 0 := by
          simpa [Polynomial.IsRoot] using hx_root_b
        have hx_eval_p_zero : p.eval x = 0 := by
          calc
            p.eval x = (a * b).eval x := by simp [hFactor]
            _ = a.eval x * b.eval x := by
              simp [Polynomial.eval_mul]
            _ = 0 := by simp [hx_eval_b_zero]
        have hx_root_p : p.IsRoot x := by
          simpa [Polynomial.IsRoot] using hx_eval_p_zero
        -- Step 5.3.6.12: Contradict the assumption that `p` has no roots.
        have hFalse : False := hroot x hx_root_p
        exact hFalse.elim

end Polynomial


/-Informal Statement

Let $F = \mathbb{Z}_7$ and let $p(x) = x^3 - 2$ and $q(x) = x^3 + 2$ be in $F[x]$. Show that $p(x)$ and $q(x)$ are irreducible in $F[x]$ and that the fields $F[x]/(p(x))$ and $F[x]/(q(x))$ are isomorphic.
-/

/-Informal Proof

We have that $p(x)$ and $q(x)$ are irreducible if they have no roots in $\mathbb{Z}_7$, which can easily be checked. E.g. for $p(x)$ we have that $p(0)=5, p(1)=6, p(2)=6, p(3)=4, p(4)=6$, $p(5)=4, p(6)=4$, and similarly for $q(x)$.

We have that every element of $F[x] /(p(x))$ is equal to $a x^2+b x+c+(p(x))$, and likewise for $F[x] /(q(x))$. We consider a map $\tau$ : $F[x] /(p(x)) \rightarrow F[x] /(q(x))$ given by
$$
\tau\left(a x^2+b x+c+(p(x))\right)=a x^2-b x+c+(q(x)) .
$$
This map is obviously onto, and since $|F[x] /(p(x))|=|F[x] /(q(x))|=7^3$ by Problem 16, it is also one-to-one. We claim that it is a homomorphism. Additivity of $\tau$ is immediate by the linearity of addition of polynomial coefficient, so we just have to check the multiplicativity; if $n=a x^2+b x+$ $c+(p(x))$ and $m=d x^2+e x+f+(p(x))$ then
$$
\begin{aligned}
\tau(n m) & =\tau\left(a d x^4+(a e+b d) x^3+(a f+b e+c d) x^2+(b f+c e) x+c f+(p(x))\right) \\
& =\tau\left(2 a d x+2(a e+b d)+(a f+b e+c d) x^2+(b f+c e) x+c f+(p(x))\right) \\
& =\tau\left((a f+b e+c d) x^2+(b f+c e+2 a d) x+(c f+2 a e+2 b d)+(p(x))\right) \\
& =(a f+b e+c d) x^2-(b f+c e+2 a d) x+c f+2 a e+2 b d+(q(x)) \\
& =a d x^4-(a e+b d) x^3+(a f+b e+c d) x^2-(b f+c e) x+c f+(q(x)) \\
& =\left(a x^2-b x+c+(q(x))\right)\left(d x^2-e x+f+(q(x))\right) \\
& =\tau(n) \tau(m) .
\end{aligned}
$$
where in the second equality we used that $x^3+p(x)=2+p(x)$ and in the fifth we used that $x^3+$ $q(x)=-2+q(x)$
-/

theorem Herstein_exercise_4_5_23 {p q: Polynomial (ZMod 7)}
  (hp : p = X^3 - 2) (hq : q = X^3 + 2) :
  Irreducible p ∧ Irreducible q ∧
  (Nonempty $ Polynomial (ZMod 7) ⧸ span ({p} : Set $ Polynomial $ ZMod 7) ≃+*
  Polynomial (ZMod 7) ⧸ span ({q} : Set $ Polynomial $ ZMod 7)) := by
  classical
  -- Step 1: Register that `7` is prime, so `ZMod 7` is a field and nontrivial.
  -- This instance will be used implicitly by degree computations and irreducibility facts.
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  -- Step 2: Prove that the specific cubic `X^3 - 2` has degree three.
  -- We treat it as a polynomial in `P` and then use `irreducible_of_degree_three_of_no_root`.
  have hdeg_p :
      (Polynomial.degree (X ^ 3 - (2 : Polynomial (ZMod 7)))) = (3 : WithBot ℕ) := by
    -- Step 2.1: Use the general lemma `degree_X_pow_sub_C` with `n = 3` and `a = 2`.
    -- This lemma says that `degree (X^n - C a) = n` for `n > 0` in a nontrivial ring.
    simpa using
      (Polynomial.degree_X_pow_sub_C (R := ZMod 7) (n := 3)
        (hn := by decide) (a := (2 : ZMod 7)))

  -- Step 3: Show that `X^3 - 2` has no roots in `ZMod 7`.
  have hno_root_p :
      ∀ x : ZMod 7,
        ¬ (X ^ 3 - (2 : Polynomial (ZMod 7))).IsRoot x := by
    -- Step 3.1: Fix an arbitrary element `x : ZMod 7` and assume it is a root.
    intro x hx
    -- `hx` is the statement that evaluating the polynomial at `x` gives `0`.
    have hEval :
        Polynomial.eval x (X ^ 3 - (2 : Polynomial (ZMod 7))) = 0 := by
      simpa [Polynomial.IsRoot] using hx
    -- Step 3.2: Simplify the evaluation `eval x` of `X^3 - 2`.
    -- The evaluation map sends `X` to `x` and preserves ring operations,
    -- so `X^3 - 2` becomes `x^3 - 2` in `ZMod 7`.
    have hpoly : x ^ 3 - (2 : ZMod 7) = 0 := by
      simpa using hEval
    -- Step 3.3: From `x^3 - 2 = 0` we deduce `x^3 = 2`.
    have hx_cube : x ^ 3 = (2 : ZMod 7) := by
      simpa [sub_eq_zero] using hpoly
    -- Step 3.4: This contradicts the lemma `no_cube_eq_two_ZMod7`.
    exact no_cube_eq_two_ZMod7 x hx_cube

  -- Step 4: Apply the general degree–3 irreducibility lemma to `X^3 - 2`.
  -- This yields irreducibility of the concrete polynomial `X^3 - 2` in `ZMod 7[X]`.
  have h_irred_X3_sub_two :
      Irreducible (X ^ 3 - (2 : Polynomial (ZMod 7))) :=
    Polynomial.irreducible_of_degree_three_of_no_root hdeg_p hno_root_p

  -- Step 5: Repeat the same reasoning for the cubic `X^3 + 2`.
  -- Step 5.1: First, compute its degree.
  have hdeg_q :
      (Polynomial.degree (X ^ 3 + (2 : Polynomial (ZMod 7)))) = (3 : WithBot ℕ) := by
    -- Step 5.1.1: Rewrite `X^3 + 2` as `X^3 - (-2)` and apply the same lemma.
    simpa [sub_eq_add_neg] using
      (Polynomial.degree_X_pow_sub_C (R := ZMod 7) (n := 3)
        (hn := by decide) (a := (-2 : ZMod 7)))

  -- Step 5.2: Show that `X^3 + 2` has no roots in `ZMod 7`.
  have hno_root_q :
      ∀ x : ZMod 7,
        ¬ (X ^ 3 + (2 : Polynomial (ZMod 7))).IsRoot x := by
    -- Step 5.2.1: Fix `x : ZMod 7` and assume it is a root.
    intro x hx
    have hEval :
        Polynomial.eval x (X ^ 3 + (2 : Polynomial (ZMod 7))) = 0 := by
      simpa [Polynomial.IsRoot] using hx
    -- Step 5.2.2: Simplify the evaluation `eval x` of `X^3 + 2` to `x^3 + 2`.
    have hpoly : x ^ 3 + (2 : ZMod 7) = 0 := by
      simpa using hEval
    -- Step 5.2.3: From `x^3 + 2 = 0` deduce `x^3 = -2`.
    have hx_cube : x ^ 3 = (-2 : ZMod 7) := by
      -- Rearranging `x^3 + 2 = 0` gives `x^3 = -2`.
      simpa using (eq_neg_of_add_eq_zero_left hpoly)
    -- Step 5.2.4: This contradicts the lemma forbidding cubes equal to `-2`.
    exact no_cube_eq_neg_two_ZMod7 x hx_cube

  -- Step 5.3: Apply the degree–3 lemma to `X^3 + 2`.
  have h_irred_X3_add_two :
      Irreducible (X ^ 3 + (2 : Polynomial (ZMod 7))) :=
    Polynomial.irreducible_of_degree_three_of_no_root hdeg_q hno_root_q

  -- Step 6: Transfer irreducibility from the concrete cubics to the parameters `p` and `q`.
  -- Since `p = X^3 - 2` and `q = X^3 + 2`, irreducibility of these cubics implies
  -- irreducibility of `p` and `q`.
  have hp_irred : Irreducible p := by
    -- Step 6.1: Rewrite `p` as `X^3 - 2` and reuse `h_irred_X3_sub_two`.
    simpa [hp] using h_irred_X3_sub_two
  have hq_irred : Irreducible q := by
    -- Step 6.2: Rewrite `q` as `X^3 + 2` and reuse `h_irred_X3_add_two`.
    simpa [hq] using h_irred_X3_add_two

  -- Step 7: Use the substitution automorphism `X ↦ -X` constructed above.
  -- We view it as a ring homomorphism `φ` on `ZMod 7[X]`.
  let φ : Polynomial (ZMod 7) →+* Polynomial (ZMod 7) := negXSubst

  -- Step 7.1: Record that `φ` is an involution (applying it twice gives the identity).
  have hφ_involutive :
      Function.Involutive (fun f : Polynomial (ZMod 7) => φ f) := by
    -- This is just `negXSubst_involutive` rewritten using the definition of `φ`.
    simpa [φ] using
      (negXSubst_involutive :
        Function.Involutive (fun f : ZMod7Poly => negXSubst f))

  -- Step 7.2: From the involutive property, deduce that `φ` is bijective.
  have hφ_bijective :
      Function.Bijective (fun f : Polynomial (ZMod 7) => φ f) :=
    Function.Involutive.bijective hφ_involutive

  -- Step 7.3: Package `φ` as a ring equivalence `φEquiv : ZMod 7[X] ≃+* ZMod 7[X]`.
  let φEquiv :
      Polynomial (ZMod 7) ≃+* Polynomial (ZMod 7) :=
    RingEquiv.ofBijective φ hφ_bijective

  -- Step 8: Compute the image of the cubic `X^3 - 2` under `φEquiv`.
  -- Substituting `X` by `-X` in `X^3 - 2` gives
  --   `(-X)^3 - 2 = -X^3 - 2 = -(X^3 + 2)`.
  have hφ_p :
      φEquiv (X ^ 3 - (2 : Polynomial (ZMod 7))) =
      -(X ^ 3 + (2 : Polynomial (ZMod 7))) := by
    -- The underlying function of `φEquiv` is `φ = negXSubst`,
    -- and `negXSubst` is given explicitly by `negXSubst_apply`.
    change
      φ (X ^ 3 - (2 : Polynomial (ZMod 7))) =
        -(X ^ 3 + (2 : Polynomial (ZMod 7)))
    -- Now use the explicit description of `φ` as composition with `-X`.
    simp [φ, negXSubst_apply, sub_eq_add_neg, pow_succ,
      add_comm, mul_comm]

  -- Step 8.1: Translate this computation to the abstract polynomials `p` and `q`.
  have hφ_p_general :
      φEquiv p = -q := by
    simpa [hp, hq] using hφ_p

  -- Step 9: Understand how the principal ideal generated by `p` behaves under `φEquiv`.
  -- Since `φEquiv p = -q`, the image of the ideal `(p)` is the ideal generated by `-q`,
  -- which coincides with the ideal generated by `q` because `-1` is a unit.
  have hmap :
      Ideal.map (φEquiv.toRingHom)
        (span ({p} : Set (Polynomial (ZMod 7)))) =
      span ({q} : Set (Polynomial (ZMod 7))) := by
    -- Step 9.1: First identify the image of `(p)` with the ideal generated by `φEquiv p = -q`.
    have hmap' :
        Ideal.map (φEquiv.toRingHom)
          (span ({p} : Set (Polynomial (ZMod 7)))) =
        span ({-q} : Set (Polynomial (ZMod 7))) := by
      -- Step 9.1.1: The image of the principal ideal `(p)` is generated by `φEquiv p`.
      have hmap0 :
          Ideal.map (φEquiv.toRingHom)
            (span ({p} : Set (Polynomial (ZMod 7)))) =
          span ({φEquiv p} : Set (Polynomial (ZMod 7))) := by
        simp [Ideal.map_span, Set.image_singleton]
      -- Step 9.1.2: Rewrite `φEquiv p` as `-q` using `hφ_p_general`.
      rw [hmap0, hφ_p_general]
    -- Step 9.2: Show that the ideals generated by `q` and `-q` coincide.
    -- This uses the fact that the constant polynomial `-1` is a unit.
    have hspan :
        span ({-q} : Set (Polynomial (ZMod 7))) =
        span ({q} : Set (Polynomial (ZMod 7))) := by
      -- Step 9.2.1: Prove that `-1 : Polynomial (ZMod 7)` is a unit.
      have hunit : IsUnit (-1 : Polynomial (ZMod 7)) := by
        exact isUnit_neg_one
      -- Step 9.2.2: Use the lemma stating that multiplying a generator by a unit
      -- does not change the principal ideal it generates.
      have hspan' :
          span ({q * (-1 : Polynomial (ZMod 7))} :
            Set (Polynomial (ZMod 7))) =
          span ({q} : Set (Polynomial (ZMod 7))) :=
        Ideal.span_singleton_mul_right_unit
          (h2 := hunit) (x := q)
      -- Step 9.2.3: Since `q * (-1) = -q` in a commutative ring, rewrite.
      rw [show -q = q * (-1 : Polynomial (ZMod 7)) from by ring]
      exact hspan'
    -- Step 9.3: Combine the two descriptions of the image ideal.
    rw [hmap', hspan]

  -- Step 9.4: Rewrite the equality of ideals into the form expected by `Ideal.quotientEquiv`.
  have hIJ :
      span ({q} : Set (Polynomial (ZMod 7))) =
        Ideal.map (φEquiv.toRingHom)
          (span ({p} : Set (Polynomial (ZMod 7)))) := by
    -- `Ideal.quotientEquiv` requires the equality `J = Ideal.map (↑φEquiv) I`.
    -- Our lemma `hmap` states the same equality with the sides reversed.
    simpa [hmap] using hmap.symm

  -- Step 10: Use `Ideal.quotientEquiv` to build an isomorphism between the quotient rings
  -- `P ⧸ (p)` and `P ⧸ (q)` induced by the ring equivalence `φEquiv`.
  let iso :
      Polynomial (ZMod 7) ⧸ span ({p} : Set (Polynomial (ZMod 7))) ≃+*
      Polynomial (ZMod 7) ⧸ span ({q} : Set (Polynomial (ZMod 7))) :=
    Ideal.quotientEquiv
      (span ({p} : Set (Polynomial (ZMod 7))))
      (span ({q} : Set (Polynomial (ZMod 7))))
      φEquiv
      hIJ

  -- Step 11: Collect all the pieces into the final statement.
  -- We return the irreducibility of `p` and `q` together with the existence
  -- of a ring isomorphism between the two quotient fields.
  refine ⟨hp_irred, hq_irred, ?_⟩
  -- Step 11.1: Package the isomorphism into a `Nonempty` witness.
  exact ⟨iso⟩
