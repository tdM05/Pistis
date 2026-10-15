import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-!
We follow the structure of the informal proof very closely.

Auxiliary idea: for any group elements `a b` and any natural number `k`,
the word `(b * a)^(k + 1)` can be rewritten as `b * (a * b)^k * a`.  We
use this to obtain the key identities

* `(a * b)^(n - 1)   = b^(n - 1) * a^(n - 1)`
* `a^n * b^(n - 1)   = b^(n - 1) * a^n`,

valid for all `a b : G`.  From there we show

* `(a * b)^(n * (n - 1)) = (b * a)^(n * (n - 1))`,

and finally convert this into the desired statement about the
commutator `(a * b * a⁻¹ * b⁻¹)`.
-/

/-!
Step 0.

Purely group–theoretic helper lemma: expand `(b * a)^(k + 1)` as
`b * (a * b)^k * a`.  This does **not** use the hypothesis `h` about
the special power `n`; it is just a structural lemma about words in a
group.
-/

lemma pow_mul_succ {G : Type*} [Group G] (a b : G) :
    ∀ k : ℕ, (b * a) ^ (k + 1) = b * (a * b) ^ k * a := by
  -- Step 0.1: We prove the lemma by induction on `k`.
  intro k
  -- Step 0.2: Do induction on `k`.
  induction k with
  | zero =>
      -- Step 0.2.1: Base case `k = 0`.
      -- LHS: `(b * a)^(0 + 1) = (b * a)^1 = b * a`.
      -- RHS: `b * (a * b)^0 * a = b * 1 * a = b * a`.
      -- We let `simp` justify these equalities.
      simp
  | succ k hk =>
      -- Step 0.2.2: Inductive step `k ↦ k + 1`.
      -- Inductive hypothesis:
      --   `(b * a)^(k + 1) = b * (a * b)^k * a`.
      -- Goal:
      --   `(b * a)^((k + 1) + 1) = b * (a * b)^(k + 1) * a`.
      -- Step 0.2.2.1: Rewrite the left-hand side using `pow_succ`.
      have hk' : (b * a) ^ (Nat.succ k) = b * (a * b) ^ k * a := by
        -- Here `Nat.succ k = k + 1`, so this is just `hk` with a different notation.
        simpa [Nat.succ_eq_add_one] using hk
      calc
        (b * a) ^ (Nat.succ k + 1)
            = (b * a) ^ (Nat.succ k) * (b * a) := by
                -- Step 0.2.2.2: One more step of exponentiation:
                -- `(b * a)^(m + 1) = (b * a)^m * (b * a)` for `m = Nat.succ k`.
                simpa [Nat.succ_eq_add_one] using
                  (pow_succ (b * a) (Nat.succ k))
        _ = (b * (a * b) ^ k * a) * (b * a) := by
                -- Step 0.2.2.3: Substitute the induction hypothesis for `(b * a)^(Nat.succ k)`.
                simp [hk']
        _ = b * (a * b) ^ k * a * b * a := by
                -- Step 0.2.2.4: Flatten the product using associativity.
                -- We go from `((b * X * a) * (b * a))` to `b * X * a * b * a`.
                simp [mul_assoc]
        _ = b * (a * b) ^ k * (a * b) * a := by
                -- Step 0.2.2.5: Regroup `a * b` in the middle.
                -- We go from `b * X * a * b * a` to `b * X * (a * b) * a`.
                simp [mul_assoc]
        _ = b * (a * b) ^ (k + 1) * a := by
                -- Step 0.2.2.6: Recognize `(a * b)^(k + 1) = (a * b)^k * (a * b)`.
                simp [pow_succ, mul_assoc]



/-Informal Statement

Let $G$ be a group in which $(a b)^{n}=a^{n} b^{n}$ for some fixed integer $n>1$ for all $a, b \in G$. For all $a, b \in G$, prove that $\left(a b a^{-1} b^{-1}\right)^{n(n-1)}=e$.
-/

/-Informal Proof

We start with the following two intermediate results.
(1) $(a b)^{n-1}=b^{n-1} a^{n-1}$.
(2) $a^n b^{n-1}=b^{n-1} a^n$.
To prove (1), notice by the given condition for all $a, b \in G$
$(b a)^n=b^n a^n$, for some fixed integers $n>1$.
Then,
$(b a)^n=b^n a^n \Longrightarrow b .(a b)(a b) \ldots .(a b) . a=b\left(b^{n-1} a^{n-1}\right) a$, where $(a b)$ occurs $n-1$ times $\Longrightarrow(a b)^{n-1}=b^{n-1} a^{n-1}$, by cancellation law.
Hence, for all $a, b \in G$
$$
(a b)^{n-1}=b^{n-1} a^{n-1} .
$$
To prove (2), notice by the given condition for all $a, b \in G$
$(b a)^n=b^n a^n$, for some fixed integers $n>1$.
Then we have
$$
\begin{aligned}
& (b a)^n=b^n a^n \\
\Longrightarrow & b \cdot(a b)(a b) \ldots(a b) \cdot a=b\left(b^{n-1} a^{n-1}\right) a, \text { where }(a b) \text { occurs } n-1 \text { times } \\
\Longrightarrow & (a b)^{n-1}=b^{n-1} a^{n-1}, \text { by cancellation law } \\
\Longrightarrow & (a b)^{n-1}(a b)=\left(b^{n-1} a^{n-1}\right)(a b) \\
\Longrightarrow & (a b)^n=b^{n-1} a^n b \\
\Longrightarrow & a^n b^n=b^{n-1} a^n b, \text { given condition } \\
\Longrightarrow & a^n b^{n-1}=b^{n-1} a^n, \text { by cancellation law. }
\end{aligned}
$$
Therefore for all $a, b \in G$ we have
$$
a^n b^{n-1}=b^{n-1} a^n
$$
In order to show that
$$
\left(a b a^{-1} b^{-1}\right)^{n(n-1)}=e, \text { for all } a, b \in G
$$
it is enough to show that
$$
(a b)^{n(n-1)}=(b a)^{n(n-1)}, \quad \forall x, y \in G .
$$
Step 3
This is because of
$$
\begin{aligned}
(a b)^{n(n-1)}=(b a)^{n(n-1)} & \left.\Longrightarrow(b a)^{-1}\right)^{n(n-1)}(a b)^{n(n-1)}=e \\
& \Longrightarrow\left(a^{-1} b^{-1}\right)^{n(n-1)}(a b)^{n(n-1)}=e \\
& \Longrightarrow\left(\left(a^{-1} b^{-1}\right)^n\right)^{n-1}\left((a b)^n\right)(n-1)=e \\
& \Longrightarrow\left((a b)^n\left(a^{-1} b^{-1}\right)^n\right)^{n-1}=e, \text { by }(1) \\
& \Longrightarrow\left(a b a^{-1} b^{-1}\right)^{n(n-1)}=e, \text { ( given condition) }
\end{aligned}
$$
Now, it suffices to show that
$$
(a b)^{n(n-1)}=(b a)^{n(n-1)}, \quad \forall x, y \in G .
$$
Now, we have
$$
\begin{aligned}
(a b)^{n(n-1)} & =\left(a^n b^n\right)^{n-1}, \text { by the given condition } \\
& =\left(a^n b^{n-1} b\right)^{n-1} \\
& =\left(b^{n-1} a^n b\right)^{n-1}, \text { by }(2) \\
& =\left(a^n b\right)^{n-1}\left(b^{n-1}\right)^{n-1}, \text { by }(1) \\
& =b^{n-1}\left(a^n\right)^{n-1}\left(b^{n-1}\right)^{n-1}, \text { by }(1) \\
& =\left(b^{n-1}\left(a^{n-1}\right)^n\right)\left(b^{n-1}\right)^{n-1} \\
& =\left(a^{n-1}\right)^n b^{n-1}\left(b^{n-1}\right)^{n-1}, \text { by }(2) \\
& =\left(a^{n-1}\right)^n\left(b^{n-1}\right)^n \\
& =\left(a^{n-1} b^{n-1}\right)^n, \text { by }(1) \\
& =(b a)^{n(n-1)}, \text { by }(1) .
\end{aligned}
$$
This completes our proof.
-/

theorem Herstein_exercise_2_2_6c {G : Type*} [Group G] {n : ℕ} (hn : n > 1)
  (h : ∀ (a b : G), (a * b) ^ n = a ^ n * b ^ n) :
  ∀ (a b : G), (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := by
  -- Step 1: Fix arbitrary elements `a` and `b` of the group.
  intro a b

  -- Step 1.1: Record that `n ≥ 1` and `0 < n`, needed for manipulating `n - 1`.
  have hn_ge : 1 ≤ n := Nat.le_of_lt hn
  -- (Substep) `0 < n` follows from `1 < n`.
  have hn_pos : 0 < n := lt_trans (Nat.succ_pos 0) hn

  -- Step 2: First auxiliary identity (1), in full generality:
  -- For all `x y : G`,
  --     (x * y)^(n - 1) = y^(n - 1) * x^(n - 1).
  -- We prove this once and for all; later we will instantiate it
  -- with many different choices of `x` and `y`.
  have h1 :
      ∀ x y : G, (x * y) ^ (n - 1) = y ^ (n - 1) * x ^ (n - 1) := by
    -- Step 2.1: Introduce arbitrary `x` and `y`.
    intro x y
    -- Step 2.2: Apply the hypothesis `h` to the pair `(y, x)`:
    -- `(y * x)^n = y^n * x^n`.
    have h_yx := h y x
    -- Step 2.3: Use the structural lemma `pow_mul_succ` with `a := x`, `b := y`
    -- to rewrite `(y * x)^n` as `y * (x * y)^(n - 1) * x`.
    have h_yx_word :
        (y * x) ^ n = y * (x * y) ^ (n - 1) * x := by
      -- We apply `pow_mul_succ` with `k = n - 1`, and then turn
      -- `(n - 1) + 1` into `n` using `Nat.sub_add_cancel`.
      have := pow_mul_succ x y (n - 1)
      -- This gives `(y * x) ^ ((n - 1) + 1) = y * (x * y)^(n - 1) * x`.
      -- Since `n - 1 + 1 = n` when `1 ≤ n`, we rewrite the exponent.
      simpa [Nat.sub_add_cancel hn_ge] using this
    -- Step 2.4: Now equate the two expressions for `(y * x)^n`.
    -- From `h_yx_word` and `h_yx` we deduce:
    --   `y * (x * y)^(n - 1) * x = y^n * x^n`.
    have h_eq : y * (x * y) ^ (n - 1) * x = y ^ n * x ^ n := by
      -- `h_yx_word` has `(y * x)^n = ...`, while `h_yx` has
      -- `(y * x)^n = y^n * x^n`.  We chain them.
      exact h_yx_word.symm.trans h_yx
    -- Step 2.5: Rewrite the right-hand side so that we can cancel
    -- the outer `y` on the left and the outer `x` on the right.
    -- We want:
    --   `y^n = y * y^(n - 1)`  and  `x^n = x^(n - 1) * x`.
    have hy : y ^ n = y * y ^ (n - 1) := by
      -- This is `pow_succ'` with exponent `n - 1`, using that
      -- `n = (n - 1) + 1`.
      simpa [Nat.sub_add_cancel hn_ge] using
        (pow_succ' y (n - 1))
    have hx : x ^ n = x ^ (n - 1) * x := by
      -- This is `pow_succ` with exponent `n - 1`.
      simpa [Nat.sub_add_cancel hn_ge] using
        (pow_succ x (n - 1))
    -- Step 2.6: Substitute these expressions for `y^n` and `x^n`
    -- into `h_eq`.
    have h_eq' :
        y * (x * y) ^ (n - 1) * x =
          y * (y ^ (n - 1) * x ^ (n - 1)) * x := by
      -- After replacement, both sides have the same outer factors
      -- `y` on the left and `x` on the right.
      simpa [hy, hx, mul_assoc] using h_eq
    -- Step 2.7: Cancel the outer `y` on the left.
    have h_eq_inner :
        (x * y) ^ (n - 1) * x =
          (y ^ (n - 1) * x ^ (n - 1)) * x := by
      -- `mul_left_cancel` removes the common left factor `y`.
      -- First, rewrite both sides as `y * (...)`.
      have h_eq'' :
          y * ((x * y) ^ (n - 1) * x) =
            y * (y ^ (n - 1) * x ^ (n - 1) * x) := by
        simpa [mul_assoc] using h_eq'
      exact mul_left_cancel (a := y) h_eq''
    -- Step 2.8: Cancel the outer `x` on the right.
    have h1_xy :
        (x * y) ^ (n - 1) =
          y ^ (n - 1) * x ^ (n - 1) := by
      -- Eliminate the trailing `* x` by multiplying both sides on the
      -- right by `x⁻¹` and simplifying with the group laws.
      have := congrArg (fun t => t * x⁻¹) h_eq_inner
      -- Now the left-hand side simplifies to `(x * y)^(n - 1)` and the
      -- right-hand side to `y^(n - 1) * x^(n - 1)`.
      simpa [mul_assoc] using this
    -- Step 2.9: Conclude the identity (1) for this particular `x, y`.
    exact h1_xy

  -- Step 3: Second auxiliary identity (2), again in full generality:
  -- For all `x y : G`,
  --     x^n * y^(n - 1) = y^(n - 1) * x^n.
  have h2 :
      ∀ x y : G, x ^ n * y ^ (n - 1) = y ^ (n - 1) * x ^ n := by
    -- Step 3.1: Introduce arbitrary elements `x` and `y`.
    intro x y
    -- Step 3.2: Apply the main hypothesis `h` to `(x, y)`:
    -- `(x * y)^n = x^n * y^n`.
    have h_xy := h x y
    -- Step 3.3: Rewrite `y^n` and `x^n` in a way that exposes
    -- the factors `y^(n - 1)` and `x^(n - 1)`.
    have hy_succ : y ^ n = y ^ (n - 1) * y := by
      simpa [Nat.sub_add_cancel hn_ge] using
        (pow_succ y (n - 1))
    have hx_succ : x ^ n = x ^ (n - 1) * x := by
      simpa [Nat.sub_add_cancel hn_ge] using
        (pow_succ x (n - 1))
    -- Step 3.4: Build the key equality
    --   `x^n * y^(n - 1) * y = y^(n - 1) * x^n * y`.
    have h_eq :
        x ^ n * y ^ (n - 1) * y =
          y ^ (n - 1) * x ^ n * y := by
      calc
        x ^ n * y ^ (n - 1) * y
            = x ^ n * y ^ n := by
                -- Replace `y^n` by `y^(n - 1) * y`.
                simp [hy_succ, mul_assoc]
        _ = (x * y) ^ n := by
                -- From `(x * y)^n = x^n * y^n`, use the symmetric direction.
                simpa [mul_assoc] using h_xy.symm
        _ = (x * y) ^ (n - 1) * (x * y) := by
                -- Expand `(x * y)^n` as `(x * y)^(n - 1) * (x * y)`.
                simpa [Nat.sub_add_cancel hn_ge] using
                  (pow_succ (x * y) (n - 1))
        _ = (y ^ (n - 1) * x ^ (n - 1)) * (x * y) := by
                -- Replace `(x * y)^(n - 1)` by `y^(n - 1) * x^(n - 1)` via identity (1).
                simp [h1 x y, mul_assoc]
        _ = y ^ (n - 1) * x ^ (n - 1) * x * y := by
                -- Flatten the product using associativity.
                simp [mul_assoc]
        _ = y ^ (n - 1) * x ^ n * y := by
                -- Combine `x^(n - 1) * x` into `x^n` using `hx_succ`.
                simp [hx_succ, mul_assoc]
    -- Step 3.5: Cancel the common right factor `y` to obtain (2).
    have h2_xy :
        x ^ n * y ^ (n - 1) =
          y ^ (n - 1) * x ^ n := by
      -- Cancel the final `* y` by multiplying on the right with `y⁻¹`.
      have := congrArg (fun t => t * y⁻¹) h_eq
      -- The left-hand side becomes `x^n * y^(n - 1)` and the right-hand
      -- side becomes `y^(n - 1) * x^n`.
      simpa [mul_assoc] using this
    -- Step 3.6: Conclude the identity (2) for this `x, y`.
    exact h2_xy

  --------------------------------------------------------------------
  -- Step 4: Show that `(a * b)^(n * (n - 1)) = (b * a)^(n * (n - 1))`.
  --------------------------------------------------------------------
  -- This is the algebraic heart of the calculation for the powers of
  -- `a * b` and `b * a`.
  have h_ab_ba :
      (a * b) ^ (n * (n - 1)) = (b * a) ^ (n * (n - 1)) := by
    -- Step 4.1: Rewrite `(a * b)^(n * (n - 1))` using `pow_mul`
    -- and the hypothesis `h`.
    -- We use `(a * b)^(n * (n - 1)) = ((a * b)^n)^(n - 1)`,
    -- then `(a * b)^n = a^n * b^n`.
    have hb_succ : b ^ n = b ^ (n - 1) * b := by
      -- `b^n = b^(n - 1 + 1) = b^(n - 1) * b`.
      simpa [Nat.sub_add_cancel hn_ge] using
        (pow_succ b (n - 1))
    calc
      (a * b) ^ (n * (n - 1))
          = (a ^ n * b ^ n) ^ (n - 1) := by
              -- Use `pow_mul` and then replace `(a * b)^n` by `a^n * b^n`.
              simpa [h a b] using
                (pow_mul (a * b) n (n - 1))
      _ = (a ^ n * b ^ (n - 1) * b) ^ (n - 1) := by
              -- Expand `b^n` as `b^(n - 1) * b` inside the base.
              simp [hb_succ, mul_assoc]
      _ = (b ^ (n - 1) * a ^ n * b) ^ (n - 1) := by
              -- Use identity (2) with `x = a`, `y = b`:
              --   `a^n * b^(n - 1) = b^(n - 1) * a^n`.
              -- Multiply both sides of (2) on the right by `b`.
              have h2_ab := h2 a b
              -- Applying `congrArg` with `λ t => t * b` yields:
              --   `a^n * b^(n - 1) * b = b^(n - 1) * a^n * b`.
              have h2_ab' :
                  a ^ n * b ^ (n - 1) * b =
                    b ^ (n - 1) * a ^ n * b := by
                simpa [mul_assoc] using
                  congrArg (fun t => t * b) h2_ab
              -- Substitute this equality for the base of the power.
              simp [h2_ab', mul_assoc]
      _ = (a ^ n * b) ^ (n - 1) * (b ^ (n - 1)) ^ (n - 1) := by
              -- Apply identity (1) to the product
              -- `b^(n - 1) * (a^n * b)`, using:
              --   `(x * y)^(n - 1) = y^(n - 1) * x^(n - 1)`
              -- with `x = b^(n - 1)` and `y = a^n * b`.
              have h1_step := h1 (b ^ (n - 1)) (a ^ n * b)
              -- The left-hand side of `h1_step` is
              --   `(b^(n - 1) * (a^n * b))^(n - 1)`,
              -- which matches `(b^ (n - 1) * a^n * b)^(n - 1)` up to associativity.
              simpa [mul_assoc] using h1_step
      _ = b ^ (n - 1) * (a ^ n) ^ (n - 1) * (b ^ (n - 1)) ^ (n - 1) := by
              -- Apply identity (1) again to `(a^n * b)^(n - 1)`:
              --   `(a^n * b)^(n - 1) = b^(n - 1) * (a^n)^(n - 1)`.
              -- Then multiply both sides by `(b^(n - 1))^(n - 1)` on the right.
              have h1_an_b := h1 (a ^ n) b
              have h1_an_b' :
                  (a ^ n * b) ^ (n - 1) * (b ^ (n - 1)) ^ (n - 1) =
                    b ^ (n - 1) * (a ^ n) ^ (n - 1) * (b ^ (n - 1)) ^ (n - 1) := by
                simpa [mul_assoc] using
                  congrArg (fun t => t * (b ^ (n - 1)) ^ (n - 1)) h1_an_b
              -- Substitute this for the previous product.
              simpa [mul_assoc] using h1_an_b'
      _ = b ^ (n - 1) * (a ^ (n - 1)) ^ n * (b ^ (n - 1)) ^ (n - 1) := by
              -- Replace `(a^n)^(n - 1)` by `(a^(n - 1))^n` using `pow_mul`.
              -- First, `(a^n)^(n - 1) = a^(n * (n - 1))`,
              -- then use commutativity of multiplication in `ℕ` to rewrite
              -- the exponent as `(n - 1) * n`, and finally interpret this
              -- as `(a^(n - 1))^n`.
              have h_pow_swap_a :
                  (a ^ n) ^ (n - 1) = (a ^ (n - 1)) ^ n := by
                -- Start from `(a^n)^(n - 1) = a^(n * (n - 1))`.
                have h_left :
                    (a ^ n) ^ (n - 1) = a ^ (n * (n - 1)) := by
                  simpa using (pow_mul a n (n - 1)).symm
                -- Also `(a^(n - 1))^n = a^((n - 1) * n)`.
                have h_right :
                    (a ^ (n - 1)) ^ n = a ^ ((n - 1) * n) := by
                  simpa using (pow_mul a (n - 1) n).symm
                -- Combine the two equalities, using commutativity of
                -- multiplication of natural numbers.
                calc
                  (a ^ n) ^ (n - 1)
                      = a ^ (n * (n - 1)) := h_left
                  _ = a ^ ((n - 1) * n) := by
                        -- Switch the factors in the exponent.
                        simp [Nat.mul_comm]
                  _ = (a ^ (n - 1)) ^ n := h_right.symm
              -- Now substitute `h_pow_swap_a` into the product.
              simp [h_pow_swap_a, mul_assoc]
      _ = (a ^ (n - 1)) ^ n * b ^ (n - 1) * (b ^ (n - 1)) ^ (n - 1) := by
              -- Use identity (2) with `x = a^(n - 1)` and `y = b`:
              --   `(a^(n - 1))^n * b^(n - 1) = b^(n - 1) * (a^(n - 1))^n`.
              -- We want to replace the prefix `b^(n - 1) * (a^(n - 1))^n`
              -- by `(a^(n - 1))^n * b^(n - 1)`.
              have h2_an1_b := h2 (a ^ (n - 1)) b
              -- Symmetric form:
              have h2_swap :
                  b ^ (n - 1) * (a ^ (n - 1)) ^ n =
                    (a ^ (n - 1)) ^ n * b ^ (n - 1) := by
                -- Take the symmetry of `h2_an1_b`.
                simpa [mul_assoc] using h2_an1_b.symm
              -- Apply this equality to the prefix, and keep
              -- `(b^(n - 1))^(n - 1)` as a tail factor.
              have h2_swap' :
                  b ^ (n - 1) * (a ^ (n - 1)) ^ n * (b ^ (n - 1)) ^ (n - 1) =
                    (a ^ (n - 1)) ^ n * b ^ (n - 1) * (b ^ (n - 1)) ^ (n - 1) := by
                simpa [mul_assoc] using
                  congrArg (fun t => t * (b ^ (n - 1)) ^ (n - 1)) h2_swap
              -- Substitute this equality.
              simpa [mul_assoc] using h2_swap'
      _ = (a ^ (n - 1)) ^ n * (b ^ (n - 1)) ^ n := by
              -- Recognize `b^(n - 1) * (b^(n - 1))^(n - 1)` as
              -- `(b^(n - 1))^n` using `pow_add` with exponents
              -- `1` and `n - 1`.
              have hb_pow :
                  (b ^ (n - 1)) ^ n =
                    b ^ (n - 1) * (b ^ (n - 1)) ^ (n - 1) := by
                -- From `pow_add` we have:
                -- `(b^(n - 1))^(1 + (n - 1)) =
                --    (b^(n - 1))^1 * (b^(n - 1))^(n - 1)`.
                have hpow := pow_add (b ^ (n - 1)) 1 (n - 1)
                -- Rewrite `1 + (n - 1)` as `n` using `n - 1 + 1 = n`.
                have hn_eq : 1 + (n - 1) = n := by
                  simpa [Nat.add_comm] using (Nat.sub_add_cancel hn_ge)
                -- Now simplify the right-hand side using `pow_one`.
                simpa [hn_eq, pow_one] using hpow
              -- Now substitute `hb_pow` for the `b`-part.
              simp [hb_pow, mul_assoc]
      _ = (a ^ (n - 1) * b ^ (n - 1)) ^ n := by
              -- Use the main hypothesis `h` with
              -- `x = a^(n - 1)` and `y = b^(n - 1)`:
              -- `(x * y)^n = x^n * y^n`.
              -- We rewrite the product `(a^(n - 1))^n * (b^(n - 1))^n`
              -- as `(a^(n - 1) * b^(n - 1))^n`.
              have h_ab' := h (a ^ (n - 1)) (b ^ (n - 1))
              -- This gives:
              -- `(a^(n - 1) * b^(n - 1))^n =
              --    (a^(n - 1))^n * (b^(n - 1))^n`.
              -- We use the symmetric direction.
              simpa using h_ab'.symm
      _ = ((b * a) ^ (n - 1)) ^ n := by
              -- Using identity (1) with `x = b`, `y = a`:
              --   `(b * a)^(n - 1) = a^(n - 1) * b^(n - 1)`.
              -- Hence `(a^(n - 1) * b^(n - 1))^n =
              --        ((b * a)^(n - 1))^n`.
              have h1_ba := h1 b a
              simp [h1_ba]
      _ = (b * a) ^ (n * (n - 1)) := by
              -- Convert `((b * a)^(n - 1))^n` back to a single power
              -- `(b * a)^(n * (n - 1))` using `pow_mul`.
              -- First, `(b * a)^((n - 1) * n) = ((b * a)^(n - 1))^n`.
              have h_pow :
                  (b * a) ^ ((n - 1) * n) =
                    ((b * a) ^ (n - 1)) ^ n := by
                simpa using (pow_mul (b * a) (n - 1) n)
              -- Then use commutativity of multiplication in `ℕ` to
              -- rewrite `((n - 1) * n)` as `n * (n - 1)`.
              have h_pow' :
                  ((b * a) ^ (n - 1)) ^ n =
                    (b * a) ^ (n * (n - 1)) := by
                -- Symmetric form of `h_pow` plus `Nat.mul_comm`.
                simpa [Nat.mul_comm] using h_pow.symm
              -- Substitute `h_pow'`.
              simp [h_pow']

  --------------------------------------------------------------------
  -- Step 5: From equality of powers of `a * b` and `b * a`
  --         to the power of the commutator.
  --------------------------------------------------------------------
  -- We have:
  --   `(a * b)^(n * (n - 1)) = (b * a)^(n * (n - 1))`.
  -- From this we will deduce:
  --   `(a * b * a⁻¹ * b⁻¹)^(n * (n - 1)) = 1`.

  -- Step 5.1: Move everything to one side:
  --   `((b * a)^(n * (n - 1)))⁻¹ * (a * b)^(n * (n - 1)) = 1`.
  have h_eq1 :
      ((b * a) ^ (n * (n - 1)))⁻¹ *
        (a * b) ^ (n * (n - 1)) = 1 := by
    -- Multiply the equality `h_ab_ba` on the left by the inverse
    -- of `(b * a)^(n * (n - 1))`.
    have := congrArg
      (fun x => ((b * a) ^ (n * (n - 1)))⁻¹ * x) h_ab_ba
    -- The right-hand side simplifies to `1` because
    -- `x⁻¹ * x = 1`.
    simpa using this

  -- Step 5.2: Express the inverse power using `(a⁻¹ * b⁻¹)` instead
  -- of `(b * a)`.
  -- We will use:
  --   `((b * a)^k)⁻¹ = ((b * a)⁻¹)^k = (a⁻¹ * b⁻¹)^k`.
  have inv_exp_eq :
      ((b * a) ^ (n * (n - 1)))⁻¹ =
        (a⁻¹ * b⁻¹) ^ (n * (n - 1)) := by
    -- First, relate `((b * a)^k)⁻¹` with `((b * a)⁻¹)^k` via `inv_pow`.
    have h_inv :
        ((b * a)⁻¹) ^ (n * (n - 1)) =
          ((b * a) ^ (n * (n - 1)))⁻¹ := by
      simpa using
        (inv_pow (b * a) (n * (n - 1)))
    -- Then use `(b * a)⁻¹ = a⁻¹ * b⁻¹` (`mul_inv_rev`).
    calc
      ((b * a) ^ (n * (n - 1)))⁻¹
          = ((b * a)⁻¹) ^ (n * (n - 1)) := by
              simpa using h_inv.symm
      _ = (a⁻¹ * b⁻¹) ^ (n * (n - 1)) := by
              simp [mul_inv_rev]

  -- Step 5.3: Substitute this expression for the inverse into `h_eq1`.
  have h_eq2 :
      (a⁻¹ * b⁻¹) ^ (n * (n - 1)) *
        (a * b) ^ (n * (n - 1)) = 1 := by
    simpa [inv_exp_eq] using h_eq1

  -- Step 5.4: Use `pow_mul` to rewrite each large power as an
  -- `(n - 1)`-th power of an `n`-th power:
  --   `(a⁻¹ * b⁻¹)^(n * (n - 1)) = ((a⁻¹ * b⁻¹)^n)^(n - 1)`
  --   `(a * b)^(n * (n - 1))     = ((a * b)^n)^(n - 1)`.
  have h_eq3 :
      ((a⁻¹ * b⁻¹) ^ n) ^ (n - 1) *
        ((a * b) ^ n) ^ (n - 1) = 1 := by
    -- Apply `pow_mul` to both bases.
    simpa [pow_mul] using h_eq2

  -- Step 5.5: Use identity (1) with
  --   `x = (a * b) ^ n` and `y = (a⁻¹ * b⁻¹) ^ n`
  -- to combine the two `(n - 1)`-th powers.
  have h1_aux :=
    h1 ((a * b) ^ n) ((a⁻¹ * b⁻¹) ^ n)
  -- `h1_aux` states:
  --   `((a * b) ^ n * (a⁻¹ * b⁻¹) ^ n) ^ (n - 1) =
  --       ((a⁻¹ * b⁻¹) ^ n) ^ (n - 1) *
  --       ((a * b) ^ n) ^ (n - 1)`.
  have h_eq4 :
      ((a * b) ^ n * (a⁻¹ * b⁻¹) ^ n) ^ (n - 1) = 1 := by
    -- Replace the product
    --   `((a⁻¹ * b⁻¹) ^ n) ^ (n - 1) * ((a * b) ^ n) ^ (n - 1)`
    -- appearing in `h_eq3` with the left-hand side of `h1_aux`.
    simpa [h1_aux.symm] using h_eq3

  -- Step 5.6: Apply the main hypothesis `h` to the pair
  -- `(a * b, a⁻¹ * b⁻¹)` to combine the inner `n`-th powers.
  have h_ab_inv :=
    h (a * b) (a⁻¹ * b⁻¹)
  -- This gives:
  --   `((a * b) * (a⁻¹ * b⁻¹))^n =
  --       (a * b)^n * (a⁻¹ * b⁻¹)^n`.
  -- Substitute in `h_eq4`.
  have h_eq5 :
      (((a * b) * (a⁻¹ * b⁻¹)) ^ n) ^ (n - 1) = 1 := by
    simpa [h_ab_inv] using h_eq4

  -- Step 5.7: Turn the `n`-th power followed by `(n - 1)`-th power
  -- into a single power of exponent `n * (n - 1)` using `pow_mul`.
  have h_eq6 :
      ((a * b) * (a⁻¹ * b⁻¹)) ^ (n * (n - 1)) = 1 := by
    simpa [pow_mul] using h_eq5

  -- Step 5.8: Identify `(a * b) * (a⁻¹ * b⁻¹)` with the commutator
  -- `a * b * a⁻¹ * b⁻¹` using associativity.
  have h_eq7 :
      (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 := by
    simpa [mul_assoc] using h_eq6

  -- Step 5.9: Conclude the desired statement for this particular
  -- pair `a, b`.
  exact h_eq7
