import Mathlib

open Real
open scoped BigOperators



/-Informal Statement

Consider a prime $p$ of the form $4 t+1$. Show that $a$ is a primitive root modulo $p$ iff $-a$ is a primitive root modulo $p$.
-/

/-Informal Proof

Suppose that $a$ is a primitive root modulo $p$. As $p-1$ is even, $(-a)^{p-1}=a^{p-1} \equiv 1$ $(\bmod p)$
If $(-a)^n \equiv 1(\bmod p)$, with $n \in \mathbb{N}$, then $a^n \equiv(-1)^n(\bmod p)$.
Therefore $a^{2 n} \equiv 1(\bmod p)$. As $a$ is a primitive root modulo $p, p-1|2 n, 2 t| n$, so $n$ is even.

Hence $a^n \equiv 1(\bmod p)$, and $p-1 \mid n$. So the least $n \in \mathbb{N}^*$ such that $(-a)^n \equiv 1$ $(\bmod p)$ is $p-1:$ the order of $-a$ modulo $p$ is $p-1,-a$ is a primitive root modulo $p$. Conversely, if $-a$ is a primitive root modulo $p$, we apply the previous result at $-a$ to to obtain that $-(-a)=a$ is a primitive root.
-/

theorem Ireland_Rosen_exercise_4_4 {p t: ℕ} (hp0 : p.Prime) (hp1 : p = 4*t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p := by
  classical
  -- Step 1: Prepare the prime-specific infrastructure needed later on.
  -- Step 1.1: Promote the primality proof to a `Fact` so `ZMod` lemmas (like `pow_card`) can use it.
  haveI : Fact p.Prime := ⟨hp0⟩
  -- Step 1.2: Deduce that `t` is positive; otherwise we would contradict the given description of `p`.
  have ht_pos : 0 < t := by
    -- Step 1.2.1: If `t = 0`, then `p = 1`, contradicting the primality of `p`.
    have ht_ne_zero : t ≠ 0 := by
      intro ht0
      have hp_eq_one : p = 1 := by simpa [ht0] using hp1
      exact (hp0.ne_one hp_eq_one)
    -- Step 1.2.2: Convert the nonzero witness into strict positivity because `t : ℕ`.
    exact Nat.pos_of_ne_zero ht_ne_zero
  -- Step 1.3: Convert the `4 t + 1` representation and `t > 0` into the inequality `1 < p`.
  have hp_one_lt : 1 < p := by
    -- Step 1.3.1: Multiply the positivity of `t` by `4` to find `4 * t > 0`.
    have h4t_pos : 0 < 4 * t := Nat.mul_pos (by decide : 0 < 4) ht_pos
    -- Step 1.3.2: Conclude `1 < 4 * t + 1`, which rewrites to `1 < p` via `hp1`.
    simpa [hp1, Nat.succ_eq_add_one] using (Nat.succ_lt_succ h4t_pos)
  -- Step 2: Prove that no element of `ZMod p` can ever be a primitive `p`-th root of unity.
  have hNoPrimitive : ∀ x : ZMod p, ¬ IsPrimitiveRoot x p := by
    -- Step 2.1: Fix an arbitrary `x` together with a hypothetical witness `hx` of the primitive-root property.
    intro x hx
    -- Step 2.2: Evaluate the Frobenius endomorphism `y ↦ y^p`, which is the identity on `ZMod p`.
    have hFrob : x ^ p = x :=
      -- Step 2.2.1: Invoke the standard lemma `ZMod.pow_card`, saying `x ^ p = x` because `card (ZMod p) = p`.
      ZMod.pow_card (x := x)
    -- Step 2.3: Combine the primitive-root equation `x ^ p = 1` with the Frobenius identity to deduce `x = 1`.
    have hx_eq_one : x = 1 := by
      -- Step 2.3.1: Rewrite `hx.pow_eq_one` by substituting the left-hand side with `x` via `hFrob`.
      simpa [hFrob] using hx.pow_eq_one
    -- Step 2.4: Contradict the fact that any primitive root must be different from `1` when `1 < p`.
    exact (hx.ne_one hp_one_lt) hx_eq_one
  -- Step 3: Use the impossibility result to turn both directions of the equivalence into contradictions.
  constructor
  · -- Step 3.1: `a` cannot satisfy the primitive-root property, so this direction collapses to `False`.
    intro h
    exact False.elim ((hNoPrimitive a) h)
  · -- Step 3.2: The same impossibility applies to `-a`, completing the equivalence.
    intro h
    exact False.elim ((hNoPrimitive (-a)) h)


/-
## Why the Original Formalization is Wrong

The original formalization uses `IsPrimitiveRoot a p`:

    IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a) p

In Mathlib, `IsPrimitiveRoot a n` means `a` is a primitive n-th root of unity, i.e.,
`a^n = 1` and `orderOf a = n`. A "primitive root modulo p" in number theory means an
element whose multiplicative order is `p - 1 = φ(p)`, NOT an element whose order is `p`.

Using `IsPrimitiveRoot a p` requires `a^p = 1` in `ZMod p`. But by Fermat's little theorem,
`a^p = a` for all `a : ZMod p`. So `a^p = 1` forces `a = 1`, and `orderOf 1 = 1 ≠ p`
for any prime `p > 1`. Therefore `IsPrimitiveRoot a p` is FALSE for every `a : ZMod p`,
making the biconditional vacuously true (`False ↔ False`). The proof above exploits this
degeneracy and has nothing to do with the actual number-theoretic content.

## Correction

Replace `IsPrimitiveRoot a p` with `IsPrimitiveRoot a (p - 1)`, which correctly encodes
"a has multiplicative order p - 1 in ZMod p", i.e., a is a primitive root modulo p.
-/

theorem Ireland_Rosen_exercise_4_4_corrected {p t : ℕ} (_hp0 : p.Prime) (hp1 : p = 4 * t + 1)
  (a : ZMod p) :
  IsPrimitiveRoot a (p - 1) ↔ IsPrimitiveRoot (-a) (p - 1) := by
  -- Step 1: It suffices to prove one direction; the other follows by applying it to `-a`.
  suffices h : ∀ (b : ZMod p), IsPrimitiveRoot b (p - 1) → IsPrimitiveRoot (-b) (p - 1) from
    ⟨h a, fun h' => neg_neg a ▸ h (-a) h'⟩
  -- Step 2: Fix `b` with `IsPrimitiveRoot b (p - 1)` and prove `IsPrimitiveRoot (-b) (p - 1)`.
  intro b hb
  -- Step 2.1: Establish that `p - 1 = 4 * t` and is even.
  have hp_sub : p - 1 = 4 * t := by omega
  have heven : Even (p - 1) := ⟨2 * t, by omega⟩
  -- Step 2.2: Use the characterization: `IsPrimitiveRoot` iff `orderOf = p - 1`.
  rw [IsPrimitiveRoot.iff_orderOf] at hb ⊢
  -- Step 2.3: We need `orderOf (-b) = p - 1`.
  -- Step 3: Show `(-b)^(p-1) = 1` (so `orderOf (-b)` divides `p - 1`).
  have hneg_pow : (-b) ^ (p - 1) = 1 := by
    -- Step 3.1: Expand `(-b)^(p-1) = (-1)^(p-1) * b^(p-1)` using `neg_pow`.
    have h1 : (-b) ^ (p - 1) = (-1 : ZMod p) ^ (p - 1) * b ^ (p - 1) := neg_pow b (p - 1)
    -- Step 3.2: Since `p - 1` is even, `(-1)^(p-1) = 1`.
    have h2 : (-1 : ZMod p) ^ (p - 1) = 1 := heven.neg_one_pow
    -- Step 3.3: Since `orderOf b = p - 1`, we have `b^(p-1) = 1`.
    have h3 : b ^ (p - 1) = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
    -- Step 3.4: Combine.
    rw [h1, h2, h3, one_mul]
  -- Step 4: Show `orderOf (-b)` divides `p - 1`.
  have hdvd : orderOf (-b) ∣ (p - 1) := orderOf_dvd_of_pow_eq_one hneg_pow
  -- Step 5: Show `p - 1` divides `orderOf (-b)` (the harder direction).
  have hdvd_rev : (p - 1) ∣ orderOf (-b) := by
    -- Step 5.1: Let `n = orderOf (-b)`, so `(-b)^n = 1`.
    set n := orderOf (-b)
    have hn_pow : (-b) ^ n = 1 := pow_orderOf_eq_one (-b)
    -- Step 5.2: From `(-b)^n = 1`, deduce `(-1)^n * b^n = 1`.
    have hmul_one : (-1 : ZMod p) ^ n * b ^ n = 1 := by
      rw [← neg_pow b n]; exact hn_pow
    -- Step 5.3: Squaring: `(-b)^n = 1` implies `(-b)^(2n) = 1`, and since 2n is even, `b^(2n) = 1`.
    have hb2n : b ^ (2 * n) = 1 := by
      -- Step 5.3.1: `(-b)^(2n) = 1` by squaring `(-b)^n = 1`.
      have hng2n : (-b) ^ (2 * n) = 1 := by
        calc (-b) ^ (2 * n) = ((-b) ^ n) ^ 2 := by ring_nf
          _ = 1 ^ 2 := by rw [hn_pow]
          _ = 1 := one_pow 2
      -- Step 5.3.2: Since 2n is even, `(-b)^(2n) = b^(2n)`.
      have heven2n : Even (2 * n) := ⟨n, by ring⟩
      rwa [neg_pow b (2 * n), heven2n.neg_one_pow, one_mul] at hng2n
    -- Step 5.4: Since `orderOf b = p - 1`, we have `(p-1) | 2n`.
    have hpm1_dvd_2n : (p - 1) ∣ 2 * n := by
      rw [← hb]; exact orderOf_dvd_of_pow_eq_one hb2n
    -- Step 5.5: Write `p - 1 = 4t`, so `4t | 2n`, hence `2t | n`.
    have h2t_dvd_n : 2 * t ∣ n := by
      have h4t_dvd_2n : 4 * t ∣ 2 * n := hp_sub ▸ hpm1_dvd_2n
      obtain ⟨c, hc⟩ := h4t_dvd_2n
      exact ⟨c, by linarith⟩
    -- Step 5.6: Since `2t | n`, `n` is even.
    have hn_even : Even n := by
      obtain ⟨m, hm⟩ := h2t_dvd_n
      exact ⟨t * m, by linarith⟩
    -- Step 5.7: Since `n` is even, `(-1)^n = 1`, so from `(-1)^n * b^n = 1` we get `b^n = 1`.
    have hbn_one : b ^ n = 1 := by
      have : (-1 : ZMod p) ^ n = 1 := hn_even.neg_one_pow
      simpa [this] using hmul_one
    -- Step 5.8: Since `orderOf b = p - 1` and `b^n = 1`, we have `(p-1) | n`.
    have : orderOf b ∣ n := orderOf_dvd_of_pow_eq_one hbn_one
    rwa [hb] at this
  -- Step 6: Conclude from mutual divisibility: orderOf (-b) = p - 1.
  exact Nat.dvd_antisymm hdvd hdvd_rev
