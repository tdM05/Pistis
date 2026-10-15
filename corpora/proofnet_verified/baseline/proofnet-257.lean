import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $G$ is a group in which $(a b)^{i}=a^{i} b^{i}$ for three consecutive integers $i$, prove that $G$ is abelian.
-/

/-Informal Proof

Let $G$ be a group, $a, b \in G$ and $i$ be any integer. Then from given condition,
$$
\begin{aligned}
(a b)^i & =a^i b^i \\
(a b)^{i+1} & =a^{i+1} b^{i+1} \\
(a b)^{i+2} & =a^{i+2} b^{i+2}
\end{aligned}
$$
From first and second, we get
$$
a^{i+1} b^{i+1}=(a b)^i(a b)=a^i b^i a b \Longrightarrow b^i a=a b^i
$$
From first and third, we get
$$
a^{i+2} b^{i+2}=(a b)^i(a b)^2=a^i b^i a b a b \Longrightarrow a^2 b^{i+1}=b^i a b a
$$
This gives
$$
a^2 b^{i+1}=a\left(a b^i\right) b=a b^i a b=b^i a^2 b
$$
Finally, we get
$$
b^i a b a=b^i a^2 b \Longrightarrow b a=a b
$$
This shows that $G$ is Abelian.
-/

theorem Herstein_exercise_2_2_3 {G : Type*} [Group G]
  {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
  (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2)) :
  ∀ a b : G, a*b = b*a := by
  -- Step 1: Fix arbitrary elements `a` and `b` of the group whose commutativity we must show.
  intro a b
  -- Step 2: Obtain an index `n` for which the power identity holds at `n`, `n+1`, and `n+2`.
  obtain ⟨n, hchain⟩ := hP1
  -- Step 2.1: Translate `P n` into the explicit equation `(a * b)^n = a^n * b^n` for all `a`, `b`.
  have hPn : ∀ a b : G, (a * b) ^ n = a ^ n * b ^ n := by
    simpa [hP] using hchain.1
  -- Step 2.2: Likewise translate `P (n + 1)` into the corresponding equality for the exponent `n + 1`.
  have hPn1 : ∀ a b : G, (a * b) ^ (n + 1) = a ^ (n + 1) * b ^ (n + 1) := by
    simpa [hP] using hchain.2.1
  -- Step 2.3: Finally translate `P (n + 2)` into an explicit equality for the exponent `n + 2`.
  have hPn2 : ∀ a b : G, (a * b) ^ (n + 2) = a ^ (n + 2) * b ^ (n + 2) := by
    simpa [hP] using hchain.2.2
  -- Step 3: Build a helper lemma showing that two consecutive equalities force each `b^k` to commute with every `a`.
  have aux :
      ∀ {k},
        (∀ a b : G, (a * b) ^ k = a ^ k * b ^ k) →
        (∀ a b : G, (a * b) ^ (k + 1) = a ^ (k + 1) * b ^ (k + 1)) →
        ∀ a b : G, Commute a (b ^ k) := by
    -- Step 3.1: Fix the index `k` and elements `x`, `y`, along with the two consecutive equalities.
    intro k hk hk1 x y
    -- Step 3.2: Rewrite the `(k + 1)` equality so every factor is expanded and `(x * y)^k` is replaced via `hk`.
    have hk1xy : ((x ^ k * y ^ k) * x) * y = ((x ^ k * x) * y ^ k) * y := by
      simpa [pow_succ, hk x y, mul_assoc] using hk1 x y
    -- Step 3.3: Cancel the common rightmost factor `y` to obtain an identity involving only the preceding factors.
    have hk1xy_no_y : (x ^ k * y ^ k) * x = (x ^ k * x) * y ^ k := by
      exact mul_right_cancel hk1xy
    -- Step 3.4: Regroup the remaining terms so that `x ^ k` is a common left factor on both sides.
    have hk1xy_regroup : x ^ k * (y ^ k * x) = x ^ k * (x * y ^ k) := by
      simpa [mul_assoc] using hk1xy_no_y
    -- Step 3.5: Cancel the left factor `x ^ k` to see directly that `y ^ k` commutes with `x`.
    have hk1xy_comm : y ^ k * x = x * y ^ k := by
      exact mul_left_cancel hk1xy_regroup
    -- Step 3.6: Package the commuting relation as an instance of `Commute`.
    exact by
      simpa [Commute] using hk1xy_comm.symm
  -- Step 4: Apply the helper lemma with `k = n` to deduce that every `b ^ n` commutes with every `a`.
  have commPowN : ∀ a b : G, Commute a (b ^ n) := aux hPn hPn1
  -- Step 5: Apply the helper lemma with `k = n + 1` to deduce that `b ^ (n + 1)` is also central.
  have commPowN1 : ∀ a b : G, Commute a (b ^ (n + 1)) := aux hPn1 hPn2
  -- Step 6: Instantiate the two commutation facts at our fixed elements `a` and `b`.
  have h_comm_n : Commute a (b ^ n) := commPowN a b
  have h_comm_n1 : Commute a (b ^ (n + 1)) := commPowN1 a b
  -- Step 6.1: Use `Commute.inv_right` to see that `a` also commutes with the inverse of `b ^ n`.
  have h_comm_inv : Commute a ((b ^ n)⁻¹) := h_comm_n.inv_right
  -- Step 6.2: Combine the commutation relations to show that `a` commutes with `(b ^ n)⁻¹ * b ^ (n + 1)`.
  have h_comm_prod : Commute a ((b ^ n)⁻¹ * b ^ (n + 1)) := h_comm_inv.mul_right h_comm_n1
  -- Step 6.3: Recognize `(b ^ n)⁻¹ * b ^ (n + 1)` as exactly `b` in any group.
  have hb_rep : (b ^ n)⁻¹ * b ^ (n + 1) = b := by
    -- Step 6.3.1: Expand `b ^ (n + 1)` as `b ^ n * b` and simplify.
    calc
      (b ^ n)⁻¹ * b ^ (n + 1)
          = (b ^ n)⁻¹ * (b ^ n * b) := by
            simp [pow_succ]
      _ = ((b ^ n)⁻¹ * b ^ n) * b :=
            (mul_assoc (b ^ n)⁻¹ (b ^ n) b).symm
      _ = b := by
            simp
  -- Step 6.4: Rewrite the previous commutation statement using the identification `(b ^ n)⁻¹ * b ^ (n + 1) = b`.
  have h_comm_b : Commute a b := by
    simpa [hb_rep] using h_comm_prod
  -- Step 7: Convert the `Commute` statement back to the desired equality `a * b = b * a`.
  simpa [Commute] using h_comm_b


/-
## Why the Original Formalization is Not Faithful

The original formalization quantified the index over ℕ (natural numbers):

    {P : ℕ → Prop} {hP : P = λ i => ∀ a b : G, (a*b)^i = a^i * b^i}
    (hP1 : ∃ n : ℕ, P n ∧ P (n+1) ∧ P (n+2))

However, the informal statement says "three consecutive integers", meaning i ranges over ℤ.
Since every natural number is an integer but not vice versa, the ℕ version is a strict special
case: it cannot express hypotheses where the three consecutive integers are negative
(e.g., i = -2, -1, 0). The informal theorem implies the ℕ version, but not conversely —
so the ℕ formalization is logically weaker than the informal claim.

## Correction

We change the existential quantifier from `∃ n : ℕ` to `∃ n : ℤ`, and use integer
exponentiation `zpow` (notation `a ^ (n : ℤ)`) in place of natural-number exponentiation.
Integer powers are well-defined for groups: `g ^ (-k) = (g ^ k)⁻¹`. We also remove the
unnecessary indirection through a predicate `P` and state the hypotheses directly.

The proof strategy is unchanged:
  1. From consecutive identities at exponents k and k+1, derive that `b^k` commutes with
     all group elements.
  2. Apply this for both k = n and k = n+1.
  3. Express b as `(b^n)⁻¹ * b^(n+1)` — a product of two elements that commute with
     everything — to conclude b commutes with every element.
-/

theorem Herstein_exercise_2_2_3_corrected {G : Type*} [Group G]
  (h : ∃ n : ℤ, (∀ a b : G, (a * b) ^ n = a ^ n * b ^ n) ∧
                  (∀ a b : G, (a * b) ^ (n + 1) = a ^ (n + 1) * b ^ (n + 1)) ∧
                  (∀ a b : G, (a * b) ^ (n + 2) = a ^ (n + 2) * b ^ (n + 2))) :
  ∀ a b : G, a * b = b * a := by
  -- Step 1: Fix arbitrary elements `a` and `b` of the group whose commutativity we must show.
  intro a b
  -- Step 2: Obtain an index `n : ℤ` for which the power identity holds at `n`, `n+1`, and `n+2`.
  obtain ⟨n, hPn, hPn1, hPn2⟩ := h
  -- Step 3: Build a helper lemma showing that two consecutive identities force `b^k` to commute
  --         with every `a`. Specifically: if (a*b)^k = a^k * b^k and (a*b)^(k+1) = a^(k+1) * b^(k+1)
  --         for all a, b, then Commute a (b^k) for all a, b.
  have aux :
      ∀ {k : ℤ},
        (∀ a b : G, (a * b) ^ k = a ^ k * b ^ k) →
        (∀ a b : G, (a * b) ^ (k + 1) = a ^ (k + 1) * b ^ (k + 1)) →
        ∀ a b : G, Commute a (b ^ k) := by
    -- Step 3.1: Fix the index `k` and elements `x`, `y`, along with the two consecutive identities.
    intro k hk hk1 x y
    -- Step 3.2: Expand the (k+1) identity using zpow_add_one and hk, then normalize associativity.
    --           LHS: (x*y)^(k+1) = (x*y)^k * (x*y) = (x^k * y^k) * (x * y) = x^k * y^k * x * y
    --           RHS: x^(k+1) * y^(k+1) = (x^k * x) * (y^k * y) = x^k * x * y^k * y
    --           After normalization: ((x^k * y^k) * x) * y = ((x^k * x) * y^k) * y
    have hk1xy : ((x ^ k * y ^ k) * x) * y = ((x ^ k * x) * y ^ k) * y := by
      simpa [zpow_add_one, hk x y, mul_assoc] using hk1 x y
    -- Step 3.3: Cancel the common rightmost factor `y` from both sides.
    have hk1xy_no_y : (x ^ k * y ^ k) * x = (x ^ k * x) * y ^ k := by
      exact mul_right_cancel hk1xy
    -- Step 3.4: Regroup using associativity so that `x^k` becomes a common left factor.
    --           LHS: x^k * (y^k * x)
    --           RHS: x^k * (x * y^k)
    have hk1xy_regroup : x ^ k * (y ^ k * x) = x ^ k * (x * y ^ k) := by
      simpa [mul_assoc] using hk1xy_no_y
    -- Step 3.5: Cancel the common left factor `x^k` to obtain `y^k * x = x * y^k`.
    have hk1xy_comm : y ^ k * x = x * y ^ k := by
      exact mul_left_cancel hk1xy_regroup
    -- Step 3.6: Package the result as `Commute x (y^k)`, i.e., `x * y^k = y^k * x`.
    exact by
      simpa [Commute] using hk1xy_comm.symm
  -- Step 4: Apply the helper with k = n to deduce that `b^n` commutes with every element.
  have commPowN : ∀ a b : G, Commute a (b ^ n) := aux hPn hPn1
  -- Step 5: Apply the helper with k = n+1 to deduce that `b^(n+1)` commutes with every element.
  --         Note: we must convert `n + 2` to `n + 1 + 1` since aux expects the second argument
  --         at exponent `k + 1 = (n+1) + 1`, which Lean represents as `n + 1 + 1`.
  have hPn2' : ∀ a b : G, (a * b) ^ (n + 1 + 1) = a ^ (n + 1 + 1) * b ^ (n + 1 + 1) := by
    have : n + 1 + 1 = n + 2 := by ring
    simp only [this]; exact hPn2
  have commPowN1 : ∀ a b : G, Commute a (b ^ (n + 1)) := aux hPn1 hPn2'
  -- Step 6: Instantiate the commutation facts at our fixed elements `a` and `b`.
  have h_comm_n : Commute a (b ^ n) := commPowN a b
  have h_comm_n1 : Commute a (b ^ (n + 1)) := commPowN1 a b
  -- Step 6.1: Derive that `a` commutes with the inverse `(b^n)⁻¹` (from Commute.inv_right).
  have h_comm_inv : Commute a ((b ^ n)⁻¹) := h_comm_n.inv_right
  -- Step 6.2: Combine: `a` commutes with `(b^n)⁻¹ * b^(n+1)` (product of two commuting elements).
  have h_comm_prod : Commute a ((b ^ n)⁻¹ * b ^ (n + 1)) := h_comm_inv.mul_right h_comm_n1
  -- Step 6.3: Show that `(b^n)⁻¹ * b^(n+1) = b` using zpow_add_one and inv_mul_cancel_left.
  have hb_rep : (b ^ n)⁻¹ * b ^ (n + 1) = b := by
    -- Step 6.3.1: Expand `b^(n+1)` as `b^n * b` via zpow_add_one.
    calc
      (b ^ n)⁻¹ * b ^ (n + 1)
          = (b ^ n)⁻¹ * (b ^ n * b) := by
            simp [zpow_add_one]
    -- Step 6.3.2: Re-associate to `((b^n)⁻¹ * b^n) * b`.
      _ = ((b ^ n)⁻¹ * b ^ n) * b :=
            (mul_assoc (b ^ n)⁻¹ (b ^ n) b).symm
    -- Step 6.3.3: Simplify `(b^n)⁻¹ * b^n = 1` and `1 * b = b`.
      _ = b := by
            simp
  -- Step 6.4: Rewrite the commutation using `(b^n)⁻¹ * b^(n+1) = b` to get `Commute a b`.
  have h_comm_b : Commute a b := by
    simpa [hb_rep] using h_comm_prod
  -- Step 7: Unfold `Commute a b` to the desired equality `a * b = b * a`.
  simpa [Commute] using h_comm_b
