import Mathlib

open Real
open scoped BigOperators
open NumberTheorySymbols



/-Informal Statement

Show that $x^{4} \equiv 2(p)$ has a solution for $p \equiv 1(4)$ iff $p$ is of the form $A^{2}+64 B^{2}$.
-/

/-Informal Proof

If  $p\equiv 1\ [4]$ and if there exists $x \in \mathbb{Z}$ such that $x^4 \equiv 2\ [p]$, then
$$2^{\frac{p-1}{4} }\equiv  x^{p-1} \equiv 1 \ [p].$$ 

From Ex. 5.27, where $p = a^2 +b^2, a$ odd,  we know that $$f^{\frac{ab}{2}} \equiv 2^{\frac{p-1}{4} } \equiv 1 \ [p].$$

Since $f^2 \equiv -1\ [p]$, the order of $f$ modulo $p$ is 4, thus $4 \mid \frac{ab}{2}$, so $8\mid ab$.

As $a$ is odd, $8 | b$, then $p = A^2 + 64 B^2$ (with $A = a, B = b/8$).

\bigskip

Conversely, if $p=A^2+64 B^2$, then $p\equiv A^2 \equiv 1 \ [4]$.

Let $a=A,b=8B$. Then $$2^{\frac{p-1}{4} } \equiv f^{\frac{ab}{2}} \equiv f^{4AB} \equiv (-1)^{2AB} \equiv 1 \ [p].$$

As $2^{\frac{p-1}{4} } \equiv 1 \ [p]$, $x^4 \equiv 2 \ [p]$ has a solution in $\mathbb{Z}$ (Prop. 4.2.1) : $2$ is a biquadratic residue modulo $p$.

Conclusion : 

$$\exists A \in \mathbb{Z}, \exists B \in \mathbb{Z}\,, p = A^2+64 B^2 \iff( p\equiv 1 \ [4] \ \mathrm{and} \ \exists x \in \mathbb{Z}, \, x^4 \equiv 2 \ [p]).$$
-/


/-
## Lemma: a closed form for `χ₈`

Mathlib defines `ZMod.χ₈ : MulChar (ZMod 8) ℤ`.

For odd `n`, number theory textbooks often use the formula

`χ₈(n) = (-1)^((n^2 - 1)/8)`.

We prove this by a straightforward case split on `n % 8`.
-/

lemma chi8_eq_neg_one_pow_sq_sub_one_div_eight {n : ℕ} (hn : Odd n) :
    ZMod.χ₈ n = (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) := by
  /-
  Step 1: Case split on the value of `n % 8`.
  -/
  have hn2 : n % 2 = 1 := (Nat.odd_iff).1 hn
  have hlt : n % 8 < 8 := Nat.mod_lt n (by decide : 0 < 8)
  have h0 : 0 ≤ n % 8 := Nat.zero_le _
  interval_cases h : n % 8 using h0, hlt
  · -- Case `n % 8 = 0` contradicts `Odd n`.
    exfalso
    have : n % 2 = 0 := by
      -- Reduce mod 2 using `2 ∣ 8`.
      calc
        n % 2 = (n % 8) % 2 := by
          exact (Nat.mod_mod_of_dvd n ⟨4, rfl⟩).symm
        _ = 0 := by simp [h]
    simp [hn2] at this
  · -- Case `n % 8 = 1`.
    have hchi : ZMod.χ₈ n = 1 := by
      -- Step 1.1: Make the coercion to `ZMod 8` explicit so we can use
      -- `ZMod.χ₈_nat_eq_if_mod_eight`.
      change ZMod.χ₈ ((n : ℕ) : ZMod 8) = (1 : ℤ)
      -- Step 1.2: Use the explicit formula for `χ₈` and simplify using `n % 8 = 1` and `n % 2 = 1`.
      -- (`simp` also evaluates the resulting boolean test `1 % 8 = 1 ∨ 1 % 8 = 7`.)
      simpa [hn2, h] using (ZMod.χ₈_nat_eq_if_mod_eight n)
    -- Show the exponent is even by writing `n = 8*q + 1`.
    set q : ℕ := n / 8 with hq
    have hn_decomp : n = 8 * q + 1 := by
      have : n = 8 * q + n % 8 := by
        simpa [hq] using (Nat.div_add_mod n 8).symm
      simpa [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    have heven : Even ((n ^ 2 - 1) / 8) := by
      refine ⟨4 * q ^ 2 + q, ?_⟩
      calc
        (n ^ 2 - 1) / 8
            = (((8 * q + 1) ^ 2 - 1) / 8) := by
                simp [hn_decomp]
        _ = (((64 * q ^ 2 + 16 * q + 1) - 1) / 8) := by
              ring_nf
        _ = (64 * q ^ 2 + 16 * q) / 8 := by
              have : (64 * q ^ 2 + 16 * q + 1) - 1 = 64 * q ^ 2 + 16 * q := by
                simp [(Nat.add_sub_cancel (64 * q ^ 2 + 16 * q) 1)]
              simp [this]
        _ = (16 * (4 * q ^ 2 + q)) / 8 := by
              ring_nf
        _ = 2 * (4 * q ^ 2 + q) := by
              -- Rewrite `16 * t` as `8 * (2 * t)` and cancel the `/ 8`.
              calc
                (16 * (4 * q ^ 2 + q)) / 8 = (8 * (2 * (4 * q ^ 2 + q))) / 8 := by
                  ring_nf
                _ = 2 * (4 * q ^ 2 + q) := by
                  simp
      -- `Even` is defined using the “double” form `k + k`, so rewrite `2 * t` accordingly.
      simp [two_mul]
    have hpow : (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) = 1 := by
      simp [heven.neg_one_pow]
    simp [hchi, hpow]

  · -- Case `n % 8 = 2` contradicts `Odd n`.
    exfalso
    have : n % 2 = 0 := by
      calc
        n % 2 = (n % 8) % 2 := by
          exact (Nat.mod_mod_of_dvd n ⟨4, rfl⟩).symm
        _ = 0 := by simp [h]
    simp [hn2] at this

  · -- Case `n % 8 = 3`.
    have hchi : ZMod.χ₈ n = -1 := by
      change ZMod.χ₈ ((n : ℕ) : ZMod 8) = (-1 : ℤ)
      simpa [hn2, h] using (ZMod.χ₈_nat_eq_if_mod_eight n)
    set q : ℕ := n / 8 with hq
    have hn_decomp : n = 8 * q + 3 := by
      have : n = 8 * q + n % 8 := by
        simpa [hq] using (Nat.div_add_mod n 8).symm
      simpa [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    have hodd : Odd ((n ^ 2 - 1) / 8) := by
      refine ⟨4 * q ^ 2 + 3 * q, ?_⟩
      calc
        (n ^ 2 - 1) / 8
            = (((8 * q + 3) ^ 2 - 1) / 8) := by
                simp [hn_decomp]
        _ = (((64 * q ^ 2 + 48 * q + 9) - 1) / 8) := by
              ring_nf
        _ = (64 * q ^ 2 + 48 * q + 8) / 8 := by
              -- Cancel the final `+1 -1` (i.e. `9 - 1 = 8`).
              have hsub : (64 * q ^ 2 + 48 * q + 9) - 1 = 64 * q ^ 2 + 48 * q + 8 := by
                -- Rewrite `... + 9` as `(... + 8) + 1` and use `Nat.add_sub_cancel`.
                have hrew : 64 * q ^ 2 + 48 * q + 9 = (64 * q ^ 2 + 48 * q + 8) + 1 := by
                  ring
                calc
                  (64 * q ^ 2 + 48 * q + 9) - 1 = ((64 * q ^ 2 + 48 * q + 8) + 1) - 1 := by
                    simp [hrew]
                  _ = 64 * q ^ 2 + 48 * q + 8 := by
                    simp [(Nat.add_sub_cancel (64 * q ^ 2 + 48 * q + 8) 1)]
              simp [hsub]
        _ = (8 * (8 * q ^ 2 + 6 * q + 1)) / 8 := by
              ring_nf
        _ = 8 * q ^ 2 + 6 * q + 1 := by
              simp
        _ = 2 * (4 * q ^ 2 + 3 * q) + 1 := by
              ring
    have hpow : (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) = -1 := by
      simp [hodd.neg_one_pow]
    simp [hchi, hpow]

  · -- Case `n % 8 = 4` contradicts `Odd n`.
    exfalso
    have : n % 2 = 0 := by
      calc
        n % 2 = (n % 8) % 2 := by
          exact (Nat.mod_mod_of_dvd n ⟨4, rfl⟩).symm
        _ = 0 := by simp [h]
    simp [hn2] at this

  · -- Case `n % 8 = 5`.
    have hchi : ZMod.χ₈ n = -1 := by
      change ZMod.χ₈ ((n : ℕ) : ZMod 8) = (-1 : ℤ)
      simpa [hn2, h] using (ZMod.χ₈_nat_eq_if_mod_eight n)
    set q : ℕ := n / 8 with hq
    have hn_decomp : n = 8 * q + 5 := by
      have : n = 8 * q + n % 8 := by
        simpa [hq] using (Nat.div_add_mod n 8).symm
      simpa [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    have hodd : Odd ((n ^ 2 - 1) / 8) := by
      refine ⟨4 * q ^ 2 + 5 * q + 1, ?_⟩
      calc
        (n ^ 2 - 1) / 8
            = (((8 * q + 5) ^ 2 - 1) / 8) := by
                simp [hn_decomp]
        _ = (((64 * q ^ 2 + 80 * q + 25) - 1) / 8) := by
              ring_nf
        _ = (64 * q ^ 2 + 80 * q + 24) / 8 := by
              -- Cancel the final `+1 -1` (i.e. `25 - 1 = 24`).
              have hsub : (64 * q ^ 2 + 80 * q + 25) - 1 = 64 * q ^ 2 + 80 * q + 24 := by
                have hrew : 64 * q ^ 2 + 80 * q + 25 = (64 * q ^ 2 + 80 * q + 24) + 1 := by
                  ring
                calc
                  (64 * q ^ 2 + 80 * q + 25) - 1 = ((64 * q ^ 2 + 80 * q + 24) + 1) - 1 := by
                    simp [hrew]
                  _ = 64 * q ^ 2 + 80 * q + 24 := by
                    simp [(Nat.add_sub_cancel (64 * q ^ 2 + 80 * q + 24) 1)]
              simp [hsub]
        _ = (8 * (8 * q ^ 2 + 10 * q + 3)) / 8 := by
              ring_nf
        _ = 8 * q ^ 2 + 10 * q + 3 := by
              simp
        _ = 2 * (4 * q ^ 2 + 5 * q + 1) + 1 := by
              ring
    have hpow : (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) = -1 := by
      simp [hodd.neg_one_pow]
    simp [hchi, hpow]

  · -- Case `n % 8 = 6` contradicts `Odd n`.
    exfalso
    have : n % 2 = 0 := by
      calc
        n % 2 = (n % 8) % 2 := by
          exact (Nat.mod_mod_of_dvd n ⟨4, rfl⟩).symm
        _ = 0 := by simp [h]
    simp [hn2] at this

  · -- Case `n % 8 = 7`.
    have hchi : ZMod.χ₈ n = 1 := by
      change ZMod.χ₈ ((n : ℕ) : ZMod 8) = (1 : ℤ)
      simpa [hn2, h] using (ZMod.χ₈_nat_eq_if_mod_eight n)
    set q : ℕ := n / 8 with hq
    have hn_decomp : n = 8 * q + 7 := by
      have : n = 8 * q + n % 8 := by
        simpa [hq] using (Nat.div_add_mod n 8).symm
      simpa [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    have heven : Even ((n ^ 2 - 1) / 8) := by
      refine ⟨4 * q ^ 2 + 7 * q + 3, ?_⟩
      calc
        (n ^ 2 - 1) / 8
            = (((8 * q + 7) ^ 2 - 1) / 8) := by
                simp [hn_decomp]
        _ = (((64 * q ^ 2 + 112 * q + 49) - 1) / 8) := by
              ring_nf
        _ = (64 * q ^ 2 + 112 * q + 48) / 8 := by
              -- Cancel the final `+1 -1` (i.e. `49 - 1 = 48`).
              have hsub : (64 * q ^ 2 + 112 * q + 49) - 1 = 64 * q ^ 2 + 112 * q + 48 := by
                have hrew : 64 * q ^ 2 + 112 * q + 49 = (64 * q ^ 2 + 112 * q + 48) + 1 := by
                  ring
                calc
                  (64 * q ^ 2 + 112 * q + 49) - 1 = ((64 * q ^ 2 + 112 * q + 48) + 1) - 1 := by
                    simp [hrew]
                  _ = 64 * q ^ 2 + 112 * q + 48 := by
                    simp [(Nat.add_sub_cancel (64 * q ^ 2 + 112 * q + 48) 1)]
              simp [hsub]
        _ = (16 * (4 * q ^ 2 + 7 * q + 3)) / 8 := by
              ring_nf
        _ = 2 * (4 * q ^ 2 + 7 * q + 3) := by
              calc
                (16 * (4 * q ^ 2 + 7 * q + 3)) / 8 = (8 * (2 * (4 * q ^ 2 + 7 * q + 3))) / 8 := by
                  ring_nf
                _ = 2 * (4 * q ^ 2 + 7 * q + 3) := by
                  simp
      simp [two_mul]
    have hpow : (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) = 1 := by
      simp [heven.neg_one_pow]
    simp [hchi, hpow]


/-
## Lemma: fourth roots in a finite cyclic group

In the second half of the main exercise we will need the standard group-theoretic fact:

> In a finite cyclic group `G` of order `n`, if `4 ∣ n` and `a^(n/4)=1`, then `a` is a fourth power.

We prove exactly this “existence of a fourth root” statement.

We will apply it later with `G = (ZMod p)ˣ` (which is cyclic for prime `p`).
-/

lemma exists_pow_four_eq_of_pow_card_div_four_eq_one
    {G : Type*} [Group G] [Finite G] [IsCyclic G] {a : G}
    (hdiv : 4 ∣ Nat.card G) (ha : a ^ (Nat.card G / 4) = 1) :
    ∃ b : G, b ^ 4 = a := by
  classical
  /-
  Step 1: Choose a generator `g` of the cyclic group.

  `IsCyclic.exists_generator` gives `g` together with the statement that every element
  belongs to `Subgroup.zpowers g`.
  -/
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)

  /-
  Step 2: Name the cardinality `n = |G|` and its quarter `q = n/4`.

  We keep these as *definitions* so we can rewrite later using `simp [n, q]`.
  -/
  set n : ℕ := Nat.card G
  set q : ℕ := n / 4

  /-
  Step 3: Since `g` generates the whole finite group, its order is exactly `n`.

  This is a ready-made lemma: `orderOf_eq_card_of_forall_mem_zpowers`.
  -/
  have horder : orderOf g = n := by
    simpa [n] using (orderOf_eq_card_of_forall_mem_zpowers (g := g) hg)

  /-
  Step 4: Write the given element `a` as an integer power of `g`.

  Because `a ∈ zpowers g`, we get `a = g^m` for some `m : ℤ`.
  -/
  have ha_mem : a ∈ Subgroup.zpowers g := hg a
  rcases (Subgroup.mem_zpowers_iff.mp ha_mem) with ⟨m, hm⟩

  /-
  Step 5: Translate the hypothesis `a^q = 1` into a statement about `g` and `m`.

  We first rewrite `a` as `g^m`, then use the basic exponent rule
  `(g^m)^q = g^(m*q)` (carefully switching between nat powers and integer powers).
  -/
  have ha_pow : (g ^ m) ^ q = 1 := by
    -- `ha` is written with `Nat.card G / 4`; our `q` is definitionally that.
    simpa [hm, n, q] using ha

  have ha_zpow : g ^ (m * (q : ℤ)) = 1 := by
    -- Step 5.1: change the nat power `(^ q)` into a zpower `(^ (q : ℤ))`.
    have hnat_to_int : (g ^ m) ^ q = (g ^ m) ^ (q : ℤ) := by
      exact_mod_cast (zpow_natCast (a := g ^ m) q).symm
    -- Step 5.2: use `zpow_mul` to combine exponents.
    calc
      g ^ (m * (q : ℤ)) = (g ^ m) ^ (q : ℤ) := by
        rw [zpow_mul g m (q : ℤ)]
      _ = (g ^ m) ^ q := by
        exact_mod_cast (zpow_natCast (a := g ^ m) q)
      _ = 1 := ha_pow

  /-
  Step 6: Convert the zpower equality `g^(m*q) = 1` into a divisibility statement.

  The lemma `orderOf_dvd_iff_zpow_eq_one` says:
  `↑(orderOf g) ∣ i  ↔  g^i = 1`.
  -/
  have hdiv_mq : (n : ℤ) ∣ m * (q : ℤ) := by
    have : (orderOf g : ℤ) ∣ m * (q : ℤ) := (orderOf_dvd_iff_zpow_eq_one).2 ha_zpow
    -- Replace `orderOf g` by `n`.
    simpa [horder] using this

  /-
  Step 7: Rewrite `n` as `4*q` and cancel the common factor `q`.

  Concretely:
  - because `4 ∣ n`, we have `n = 4*q` (as natural numbers, and hence as integers);
  - from `(4*q) ∣ (m*q)` and `q ≠ 0`, we can cancel `q` and obtain `4 ∣ m`.
  -/
  have hn_int : (n : ℤ) = 4 * (q : ℤ) := by
    -- On naturals we have `4 * (n/4) = n`.
    have hnat : (4 * q : ℕ) = n := by
      simpa [n, q] using (Nat.mul_div_cancel' hdiv)
    -- Cast to integers.
    have hint : (4 * q : ℤ) = (n : ℤ) := by
      norm_cast
    -- Rearrange.
    simpa [mul_assoc, mul_comm, mul_left_comm, n, q] using hint.symm

  -- `q ≠ 0` because `n = 4*q` and a finite group has `n > 0`.
  have hq0_nat : q ≠ 0 := by
    intro hq0
    have hn0 : n = 0 := by
      have : (4 * q : ℕ) = n := by simpa [n, q] using (Nat.mul_div_cancel' hdiv)
      simpa [hq0] using this.symm
    have hnpos : 0 < n := by
      -- A group is nonempty, so a finite group has positive cardinality.
      simp [n, (Nat.card_pos (α := G))]
    exact (Nat.ne_of_gt hnpos) hn0
  have hq0 : (q : ℤ) ≠ 0 := (Int.ofNat_ne_zero).2 hq0_nat

  have h4divm : (4 : ℤ) ∣ m := by
    -- Rewrite the divisibility using `n = 4*q`.
    have : (4 : ℤ) * (q : ℤ) ∣ m * (q : ℤ) := by
      simpa [hn_int, mul_assoc, mul_comm, mul_left_comm] using hdiv_mq
    -- Cancel the common right factor `q`.
    exact Int.dvd_of_mul_dvd_mul_right hq0 this

  /-
  Step 8: Use `m = 4*t` to explicitly build a fourth root.

  We take `b = g^t`, then `(g^t)^4 = g^(t*4) = g^(4*t) = g^m = a`.
  -/
  rcases h4divm with ⟨t, rfl⟩
  refine ⟨g ^ t, ?_⟩
  -- Convert `(g^t)^4` into a zpower so we can use `zpow_mul`.
  have : (g ^ t) ^ 4 = g ^ (t * (4 : ℤ)) := by
    -- Step 8.1: rewrite the nat power as a zpower.
    have hnat_to_int : (g ^ t) ^ 4 = (g ^ t) ^ (4 : ℤ) := by
      exact_mod_cast (zpow_natCast (a := g ^ t) 4).symm
    -- Step 8.2: now apply `zpow_mul`.
    calc
      (g ^ t) ^ 4 = (g ^ t) ^ (4 : ℤ) := hnat_to_int
      _ = g ^ (t * (4 : ℤ)) := by
        rw [zpow_mul g t (4 : ℤ)]
  -- Finally, connect back to `a = g^(4*t)`.
  calc
    (g ^ t) ^ 4 = g ^ (t * (4 : ℤ)) := this
    _ = g ^ (4 * t) := by
      -- commute the integer multiplication
      simp [mul_comm]
    _ = a := by
      -- `hm : g^(4*t) = a`
      simp [hm]


/-
## Lemma (Ireland–Rosen Ex. 5.27, in `ZMod p` form)

Assume:

* `p` is a prime with `p ≡ 1 [MOD 4]`;
* `p = a^2 + b^2` with `a` odd.

Define the element `f = b / a` modulo `p`, i.e.

`f = (b : ZMod p) * (a : ZMod p)⁻¹`.

Then `f^2 = -1` and the crucial congruence holds:

`2^((p-1)/4) = f^(a*b/2)` in `ZMod p`.

This is exactly the ingredient used in the informal proof.
-/

lemma two_pow_sub_one_div_four_eq_f_pow_mul_div_two
    {p a b : ℕ} (hp : p.Prime) (hp1 : p ≡ 1 [MOD 4]) (hab : a ^ 2 + b ^ 2 = p)
    (ha : Odd a) :
    (2 : ZMod p) ^ ((p - 1) / 4) = ((b : ZMod p) * (a : ZMod p)⁻¹) ^ (a * b / 2) := by
  classical

  /-
  Step 0: Register `p` as a prime for typeclass inference (`ZMod p` is a field).
  -/
  haveI : Fact p.Prime := ⟨hp⟩

  /-
  Step 1: Extract the congruence `p % 4 = 1` and hence `p ≠ 2`.
  -/
  have hp4 : p % 4 = 1 := by simpa using hp1
  have hp_ne2 : p ≠ 2 := by
    intro hp2
    subst hp2
    /-
    Step 1.1: After substituting `p = 2`, the stored congruence becomes
    `2 % 4 = 1`, which is false.

    We let `decide` prove the *inequality* `2 % 4 ≠ 1`, and then apply it.
    -/
    have : (2 % 4 : ℕ) ≠ 1 := by decide
    exact this hp4
  haveI : Fact (2 < p) := ⟨lt_of_le_of_ne (hp.two_le) (Ne.symm hp_ne2)⟩

  /-
  Step 2: Define the key exponents.

  * `k = (p-1)/4` is the “quartic” exponent.
  * `n = a+b` will be the modulus for the Jacobi/χ₈ computation.
  -/
  set k : ℕ := (p - 1) / 4
  set n : ℕ := a + b

  /-
  Step 3: Show `4 ∣ p-1` from the hypothesis `p ≡ 1 [MOD 4]`.

  We do this by subtracting `1` on both sides of the congruence.
  -/
  have hp_ge1 : 1 ≤ p := Nat.succ_le_iff.mpr (hp.pos)
  have hp_dvd4 : 4 ∣ p - 1 := by
    -- Step 3.1: subtract `1` from both sides of `p ≡ 1 [MOD 4]`.
    have hsub : p - 1 ≡ 0 [MOD 4] := by
      -- This is `Nat.ModEq.sub` with `c = d = 1`.
      simpa using (Nat.ModEq.sub (n := 4) (a := p) (b := 1) (c := 1) (d := 1)
        hp_ge1 (by decide) hp1 Nat.ModEq.rfl)
    -- Step 3.2: a congruence to `0` is exactly divisibility.
    have : (p - 1) % 4 = 0 := by simpa using hsub
    exact (Nat.dvd_iff_mod_eq_zero).2 this

  /-
  Step 4: Define the element `f = b / a` modulo `p`.
  -/
  let f : ZMod p := (b : ZMod p) * (a : ZMod p)⁻¹

  /-
  Step 5: Prove that `(a : ZMod p) ≠ 0` so that dividing by `a` makes sense.

  We show `a < p`, hence `p ∤ a`, and then use `ZMod.natCast_eq_zero_iff`.
  -/
  have ha_sq_le : a ^ 2 ≤ p := by
    -- `a^2 ≤ a^2 + b^2 = p`.
    have : a ^ 2 ≤ a ^ 2 + b ^ 2 := Nat.le_add_right _ _
    simpa [hab] using this

  have ha_lt_p : a < p := by
    -- If `p ≤ a`, then `p^2 ≤ a^2 ≤ p`, contradiction since `p < p^2` for prime `p`.
    by_contra h
    have hpa : p ≤ a := Nat.le_of_not_gt h
    have hp2_le : p ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hpa 2
    have : p ^ 2 ≤ p := le_trans hp2_le ha_sq_le
    have hp_lt_hp2 : p < p ^ 2 := by
      /-
      Step 5.1: Prove `p < p^2`.

      We use the lemma `Nat.mul_lt_mul_left` in its iff-form:

      `p * 1 < p * p ↔ 1 < p`.

      Since `1 < p` for a prime, we get the desired strict inequality.
      -/
      have hmul : p * 1 < p * p :=
        (Nat.mul_lt_mul_left (a := p) (b := 1) (c := p) hp.pos).2 hp.one_lt
      simpa [pow_two] using hmul
    exact (not_le_of_gt hp_lt_hp2) this

  have haZ : (a : ZMod p) ≠ 0 := by
    intro ha0
    have hp_dvd_a : p ∣ a := (ZMod.natCast_eq_zero_iff a p).1 ha0
    have : a = 0 := Nat.eq_zero_of_dvd_of_lt hp_dvd_a ha_lt_p
    -- But `a` is odd, hence nonzero.
    exact (ha.pos.ne') this

  /-
  Step 6: Prove the fundamental identity `f^2 = -1` in `ZMod p`.
  -/
  have habZ : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
    -- Cast `a^2 + b^2 = p` into `ZMod p`, and use `p = 0` in `ZMod p`.
    have : ((a ^ 2 + b ^ 2 : ℕ) : ZMod p) = (p : ZMod p) := congrArg (fun t : ℕ => (t : ZMod p)) hab
    simpa using (this.trans (ZMod.natCast_self p))

  have hb_sq : (b : ZMod p) ^ 2 = - (a : ZMod p) ^ 2 :=
    eq_neg_of_add_eq_zero_right habZ

  have ha_inv_sq : (a : ZMod p) ^ 2 * ((a : ZMod p)⁻¹) ^ 2 = 1 := by
    -- This is just `(a * a⁻¹)^2 = 1^2` rewritten using `mul_pow`.
    calc
      (a : ZMod p) ^ 2 * ((a : ZMod p)⁻¹) ^ 2
          = ((a : ZMod p) * (a : ZMod p)⁻¹) ^ 2 := by
              simp [mul_pow]
      _ = 1 := by
          simp [haZ]

  have hf_sq : f ^ 2 = (-1 : ZMod p) := by
    -- Expand `f^2 = (b/a)^2 = b^2 * a^{-2}` and substitute `b^2 = -a^2`.
    calc
      f ^ 2 = (b : ZMod p) ^ 2 * ((a : ZMod p)⁻¹) ^ 2 := by
        simp [f, mul_pow]
      _ = (- (a : ZMod p) ^ 2) * ((a : ZMod p)⁻¹) ^ 2 := by
        simp [hb_sq]
      _ = - ((a : ZMod p) ^ 2 * ((a : ZMod p)⁻¹) ^ 2) := by
        ring
      _ = (-1 : ZMod p) := by
        /-
        Step 6.1: At this point it suffices to prove
        `((a : ZMod p)^2) * ((a : ZMod p)^2)⁻¹ = 1`.

        Since `a ≠ 0` in the field `ZMod p`, we also have `a^2 ≠ 0`, so `simp`
        can cancel `a^2` against its inverse.
        -/
        have ha2Z : (a : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 haZ
        simp [ha2Z]

  /-
  Step 7: Show that `b` is even and hence `n = a + b` is odd.
  -/
  have hp_odd : Odd p := by
    -- From `p % 4 = 1` we get `p % 2 = 1`.
    exact (Nat.odd_iff).2 (Nat.odd_of_mod_four_eq_one hp4)

  have hb_even : Even b := by
    -- `p = a^2 + b^2` is odd and `a^2` is odd, so `b^2` is even, hence `b` is even.
    -- Step 7.1: `a` odd implies `a^2` odd (note: the exponent is an *implicit* argument).
    have ha2_odd : Odd (a ^ 2) := by
      simpa using (ha.pow (n := 2))
    have hsum_odd : Odd (a ^ 2 + b ^ 2) := by simpa [hab] using hp_odd
    have hb2_even : Even (b ^ 2) := ((Nat.odd_add).1 hsum_odd).1 ha2_odd
    -- `Even (b^2)` implies `Even b` because the exponent is nonzero.
    exact (Nat.even_pow).1 hb2_even |>.1

  have hn_odd : Odd n := by
    -- `Odd (a + b) ↔ (Odd a ↔ Even b)`.
    have : Odd a ↔ Even b := ⟨fun _ => hb_even, fun _ => ha⟩
    simpa [n] using (Nat.odd_add).2 this

  /-
  Step 8: Compute `legendreSym p a = 1`.

  This shows that `a^((p-1)/2) = 1` in `ZMod p`, which will let us remove the factor `a`
  from `(a+b)^(p/2)`.
  -/
  have hab_coprime : Nat.Coprime a b := by
    -- Let `d = gcd a b`. Then `d ∣ a^2 + b^2 = p`.
    let d := Nat.gcd a b
    have hd1 : d ∣ a := Nat.gcd_dvd_left a b
    have hd2 : d ∣ b := Nat.gcd_dvd_right a b
    have hd_dvd : d ∣ a ^ 2 + b ^ 2 := by
      refine dvd_add ?_ ?_
      · simpa [pow_two] using dvd_mul_of_dvd_left hd1 a
      · simpa [pow_two] using dvd_mul_of_dvd_left hd2 b
    have hd_dvd_p : d ∣ p := by simpa [d, hab] using hd_dvd
    -- Since `p` is prime, `d = 1` or `d = p`. But `d ≤ a < p`, so `d ≠ p`.
    have hd_lt_p : d < p := by
      have hd_le_a : d ≤ a := Nat.gcd_le_left b ha.pos
      exact lt_of_le_of_lt hd_le_a ha_lt_p
    rcases (Nat.dvd_prime hp).1 hd_dvd_p with hd1' | hdp
    · -- `d = 1`
      exact (Nat.coprime_iff_gcd_eq_one).2 (by simpa [d] using hd1')
    · -- `d = p` contradicts `d < p`.
      exfalso
      simp [d, hdp] at hd_lt_p

  have hab_coprime_int : (b : ℤ).gcd (a : ℤ) = 1 := by
    -- Convert `Nat.gcd = 1` into the corresponding statement for `Int.gcd`.
    have : Nat.gcd b a = 1 := (Nat.coprime_iff_gcd_eq_one).1 hab_coprime.symm
    simpa [Int.gcd_natCast_natCast] using this

  have hleg_a : legendreSym p (a : ℤ) = 1 := by
    /-
    Step 8.1: Rewrite `legendreSym` as the Jacobi symbol `J(·|p)`.
    -/
    have h1 : legendreSym p (a : ℤ) = J((a : ℤ) | p) := by
      simpa using (jacobiSym.legendreSym.to_jacobiSym p (a : ℤ))
    /-
    Step 8.2: Use quadratic reciprocity (in the Jacobi-symbol form) to swap:
    `J(a|p) = J(p|a)` because `a` is odd and `p % 4 = 1`.
    -/
    have h2 : J((a : ℤ) | p) = J((p : ℤ) | a) := by
      simpa using (jacobiSym.quadratic_reciprocity_one_mod_four' ha hp4)
    /-
    Step 8.3: Reduce `p` modulo `a`.

    Since `p = a^2 + b^2`, we have `p ≡ b^2 (mod a)`.
    -/
    have hp_mod_a : (p : ℤ) % (a : ℤ) = (b ^ 2 : ℤ) % (a : ℤ) := by
      -- Work with a nat congruence first: `p % a = b^2 % a`.
      have hp_mod_a_nat : p % a = (b ^ 2) % a := by
        calc
          p % a = (a ^ 2 + b ^ 2) % a := by simp [hab.symm]
          _ = ((a ^ 2) % a + (b ^ 2) % a) % a := by simp [Nat.add_mod]
          _ = (0 + (b ^ 2) % a) % a := by
            have : (a ^ 2) % a = 0 := by
              -- because `a ∣ a^2`
              have : a ∣ a ^ 2 := by
                simp [pow_two, dvd_mul_of_dvd_left (dvd_refl a) a]
              exact Nat.mod_eq_zero_of_dvd this
            simp [this]
          _ = (b ^ 2) % a := by simp

      -- Cast the nat congruence to an int congruence.
      -- `Int.natCast_mod` rewrites casts of nat mods into int mods.
      -- We use `simp` to turn the casted equality into the desired int-mod equality.
      have : (p % a : ℤ) = ((b ^ 2) % a : ℤ) := by
        exact congrArg (fun t : ℕ => (t : ℤ)) hp_mod_a_nat
      simpa [Int.natCast_mod] using this
    /-
    Step 8.4: Apply `jacobiSym.mod_left'` and then use that squares have Jacobi symbol `1`.
    -/
    have h3 : J((p : ℤ) | a) = J((b ^ 2 : ℤ) | a) :=
      jacobiSym.mod_left' hp_mod_a
    have h4 : J((b ^ 2 : ℤ) | a) = 1 := by
      -- `J(b^2|a) = 1` because `gcd(b,a)=1`.
      simpa [pow_two] using (jacobiSym.sq_one' (a := (b : ℤ)) (b := a) hab_coprime_int)
    -- Put everything together.
    -- `legendreSym p a = J(a|p) = J(p|a) = J(b^2|a) = 1`.
    simp [h1, h2, h3, h4]

  /-
  Step 9: Use Euler's criterion: `a^(p/2) = legendreSym p a` in `ZMod p`, hence `a^(p/2)=1`.
  -/
  have ha_pow_half : (a : ZMod p) ^ (p / 2) = 1 := by
    /-
    Step 9.1: Euler's criterion in `ZMod p`:

    `((legendreSym p a : ℤ) : ZMod p) = (a : ZMod p)^(p/2)`.
    -/
    have hpow : (legendreSym p (a : ℤ) : ZMod p) = (a : ZMod p) ^ (p / 2) := by
      simpa using (legendreSym.eq_pow (p := p) (a := (a : ℤ)))

    /-
    Step 9.2: From Step 8 we already know `legendreSym p a = 1`, so the LHS is `1`.
    -/
    have hleg' : (legendreSym p (a : ℤ) : ZMod p) = 1 := by
      simp [hleg_a]

    /-
    Step 9.3: Combine Step 9.1 and Step 9.2 to conclude `(a : ZMod p)^(p/2) = 1`.
    -/
    calc
      (a : ZMod p) ^ (p / 2) = (legendreSym p (a : ℤ) : ZMod p) := by
        exact hpow.symm
      _ = 1 := hleg'

  /-
  Step 10: Compute `legendreSym p (a+b) = χ₈ (a+b)`.
  -/
  have hcoprime_bn : (b : ℤ).gcd (n : ℤ) = 1 := by
    -- `b` is coprime to `a`, hence also to `a+b`.
    have : Nat.Coprime b n := by
      -- `Coprime b (a+b) ↔ Coprime b a`.
      have : Nat.Coprime b a := hab_coprime.symm
      -- Use the simp lemma `Nat.coprime_add_self_right`.
      simpa [n, add_comm, add_left_comm, add_assoc] using
        (Nat.coprime_add_self_right (m := b) (n := a)).2 this
    have : Nat.gcd b n = 1 := (Nat.coprime_iff_gcd_eq_one).1 this
    simpa [Int.gcd_natCast_natCast] using this

  have hleg_n : legendreSym p (n : ℤ) = ZMod.χ₈ n := by
    /-
    Step 10.1: Rewrite `legendreSym` as the Jacobi symbol `J(n|p)`.
    -/
    have h1 : legendreSym p (n : ℤ) = J((n : ℤ) | p) := by
      simpa using (jacobiSym.legendreSym.to_jacobiSym p (n : ℤ))

    /-
    Step 10.2: Apply quadratic reciprocity to swap:
    `J(n|p) = J(p|n)` because `n` is odd and `p % 4 = 1`.
    -/
    have h2 : J((n : ℤ) | p) = J((p : ℤ) | n) := by
      simpa [n] using (jacobiSym.quadratic_reciprocity_one_mod_four' hn_odd hp4)

    /-
    Step 10.3: Reduce `p` modulo `n = a+b`.

    Using `p = a^2 + b^2`, one checks `p ≡ 2*b^2 (mod a+b)`.
    We prove this in ℤ using divisibility and then apply `jacobiSym.mod_left'`.
    -/
    have hp_mod_n : (p : ℤ) % (n : ℤ) = (2 * (b : ℤ) ^ 2) % (n : ℤ) := by
      -- Prove an integer congruence, then unfold `Int.ModEq`.
      have hdiv' : (n : ℤ) ∣ (2 * (b : ℤ) ^ 2) - (p : ℤ) := by
        -- Expand `p = a^2 + b^2` in ℤ.
        have hcalc : (2 * (b : ℤ) ^ 2) - (p : ℤ) = (b : ℤ) ^ 2 - (a : ℤ) ^ 2 := by
          -- `p = a^2 + b^2` so `2b^2 - p = b^2 - a^2`.
          -- We use `ring` for this algebraic manipulation.
          have hp_int : (p : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
            -- cast `a^2 + b^2 = p` into ℤ
            norm_cast
            exact hab.symm
          -- Now rewrite and ring.
          -- `ring` can handle the arithmetic on ℤ.
          -- (We rewrite `p` using `hp_int` first.)
          calc
            (2 * (b : ℤ) ^ 2) - (p : ℤ) = (2 * (b : ℤ) ^ 2) - ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) := by
              simp [hp_int]
            _ = (b : ℤ) ^ 2 - (a : ℤ) ^ 2 := by
              ring
        -- Finally, `b^2 - a^2 = (b-a) * (b+a)` is divisible by `a+b = n`.
        -- Note that `b + a = a + b = n`.
        refine ⟨(b : ℤ) - a, ?_⟩
        /-
        Step 10.3.1: Factor `b^2 - a^2` as `(b-a)*(b+a)` and rewrite `b+a` as `n`.
        -/
        have hfac : ((b : ℤ) - a) * (n : ℤ) = (b : ℤ) ^ 2 - (a : ℤ) ^ 2 := by
          -- `n = a + b`.
          have hn_int : (n : ℤ) = (a : ℤ) + (b : ℤ) := by
            -- by definition of `n`
            simp [n]
          -- factorization
          calc
            ((b : ℤ) - a) * (n : ℤ) = ((b : ℤ) - a) * ((a : ℤ) + (b : ℤ)) := by
              simp [hn_int]
            _ = (b : ℤ) ^ 2 - (a : ℤ) ^ 2 := by
              ring
        /-
        Step 10.3.2: Conclude the required equality for the chosen witness `(b-a)`.
        -/
        calc
          (2 * (b : ℤ) ^ 2) - (p : ℤ) = (b : ℤ) ^ 2 - (a : ℤ) ^ 2 := hcalc
          _ = ((b : ℤ) - a) * (n : ℤ) := by
            simp [hfac.symm]
          _ = (n : ℤ) * ((b : ℤ) - a) := by
            -- `Int` multiplication is commutative.
            simp [mul_comm]
      -- Turn the divisibility statement into a congruence.
      have hmodeq : (p : ℤ) ≡ (2 * (b : ℤ) ^ 2) [ZMOD (n : ℤ)] :=
        (Int.modEq_iff_dvd).2 hdiv'
      simpa [Int.ModEq] using hmodeq

    have h3 : J((p : ℤ) | n) = J((2 * (b : ℤ) ^ 2) | n) :=
      jacobiSym.mod_left' hp_mod_n

    /-
    Step 10.4: Split `J(2*b^2|n)` and simplify:

    * `J(2|n) = χ₈(n)` because `n` is odd;
    * `J(b^2|n) = 1` because `gcd(b,n)=1`.
    -/
    have h4 : J((2 * (b : ℤ) ^ 2) | n) = ZMod.χ₈ n := by
      calc
        J((2 * (b : ℤ) ^ 2) | n) = J(2 | n) * J((b : ℤ) ^ 2 | n) := by
          simp [(jacobiSym.mul_left (2 : ℤ) ((b : ℤ) ^ 2) n)]
        _ = ZMod.χ₈ n * 1 := by
          -- Evaluate `J(2|n)` and `J(b^2|n)`.
          have h2' : J(2 | n) = ZMod.χ₈ n := by
            simpa [n] using (jacobiSym.at_two hn_odd)
          have hsq : J((b : ℤ) ^ 2 | n) = 1 := by
            simpa [pow_two] using (jacobiSym.sq_one' (a := (b : ℤ)) (b := n) hcoprime_bn)
          simp [h2', hsq]
        _ = ZMod.χ₈ n := by simp

    -- Conclude: `legendreSym p n = J(n|p) = J(p|n) = J(2*b^2|n) = χ₈ n`.
    simp [h1, h2, h3, h4]

  /-
  Step 11: Use Euler's criterion again to express `(a+b)^(p/2)` as `χ₈(n)`.
  -/
  have hn_euler : ((n : ℤ) : ZMod p) ^ (p / 2) = (ZMod.χ₈ n : ZMod p) := by
    -- `legendreSym.eq_pow` gives `(legendreSym p n : ZMod p) = (n : ZMod p)^(p/2)`.
    have hpow := legendreSym.eq_pow (p := p) (a := (n : ℤ))
    -- Rewrite `legendreSym p n` as `χ₈ n`.
    have hcast : (legendreSym p (n : ℤ) : ZMod p) = (ZMod.χ₈ n : ZMod p) := by
      simp [hleg_n]
    -- Solve for the desired direction.
    exact hpow.symm.trans hcast

  /-
  Step 12: Rewrite `n = a*(1+f)` in `ZMod p`, and compute `n^(p/2)`.
  -/
  have haf : (a : ZMod p) * f = (b : ZMod p) := by
    -- Expand `f = b * a⁻¹` and commute factors so that `a * a⁻¹` appears.
    calc
      (a : ZMod p) * f = (a : ZMod p) * ((b : ZMod p) * (a : ZMod p)⁻¹) := by rfl
      _ = (b : ZMod p) * ((a : ZMod p) * (a : ZMod p)⁻¹) := by
        ring
      _ = (b : ZMod p) := by
        simp [haZ]

  have hnZ : ((n : ℕ) : ZMod p) = (a : ZMod p) * (1 + f) := by
    calc
      ((n : ℕ) : ZMod p) = (a : ZMod p) + (b : ZMod p) := by
        -- `n = a + b` by definition.
        simp [n]
      _ = (a : ZMod p) + (a : ZMod p) * f := by
        -- replace `b` by `a*f`
        simp [haf]
      _ = (a : ZMod p) * (1 + f) := by
        ring

  /-
  Step 13: Show that `p/2 = 2*k`.

  This lets us rewrite `(1+f)^(p/2)` as `((1+f)^2)^k`.
  -/
  have hp_div_two : p / 2 = 2 * k := by
    have hp_odd' : Odd p := hp_odd
    /-
    Step 13.1: Convert `Odd p` to the remainder statement `p % 2 = 1`.
    -/
    have hp2 : p % 2 = 1 := by
      simpa using (Nat.odd_iff).1 hp_odd'
    /-
    Step 13.2: For odd `p`, we have `2*(p/2) = p-1`.
    -/
    have h1 : 2 * (p / 2) = p - 1 := Nat.two_mul_odd_div_two hp2
    -- `4*k = p-1` because `k = (p-1)/4` and `4 ∣ p-1`.
    have h2 : 4 * k = p - 1 := by
      simpa [k] using (Nat.mul_div_cancel' hp_dvd4)
    /-
    Step 13.3: Rewrite `4*k` as `2*(2*k)` and cancel the common factor `2`.
    -/
    have h' : 2 * (p / 2) = 2 * (2 * k) := by
      calc
        2 * (p / 2) = p - 1 := h1
        _ = 4 * k := by
          simpa using h2.symm
        _ = 2 * (2 * k) := by
          ring
    exact Nat.mul_left_cancel (by decide : 0 < (2 : ℕ)) h'

  /-
  Step 14: Compute `(n : ZMod p)^(p/2)` in terms of `f` and `2`.

  Using `n = a*(1+f)` and `a^(p/2) = 1`, we get
  `n^(p/2) = (1+f)^(p/2)`.

  Moreover `(1+f)^2 = 2*f` because `f^2 = -1`.
  -/
  have h1pf_sq : (1 + f) ^ 2 = (2 : ZMod p) * f := by
    calc
      (1 + f) ^ 2 = 1 + (2 : ZMod p) * f + f ^ 2 := by
        ring
      _ = 1 + (2 : ZMod p) * f + (-1 : ZMod p) := by
        simp [hf_sq]
      _ = (2 : ZMod p) * f := by
        ring

  have hn_pow_calc : ((n : ℕ) : ZMod p) ^ (p / 2) = (2 : ZMod p) ^ k * f ^ k := by
    -- Start from `n = a*(1+f)`.
    calc
      ((n : ℕ) : ZMod p) ^ (p / 2) = ((a : ZMod p) * (1 + f)) ^ (p / 2) := by
        simp [hnZ]
      _ = (a : ZMod p) ^ (p / 2) * (1 + f) ^ (p / 2) := by
        simp [mul_pow]
      _ = (1 + f) ^ (p / 2) := by
        -- use `a^(p/2) = 1`
        simp [ha_pow_half]
      _ = (1 + f) ^ (2 * k) := by
        simp [hp_div_two]
      _ = ((1 + f) ^ 2) ^ k := by
        -- `x^(2*k) = (x^2)^k`
        simp [(pow_mul (1 + f) 2 k)]
      _ = ((2 : ZMod p) * f) ^ k := by
        simp [h1pf_sq]
      _ = (2 : ZMod p) ^ k * f ^ k := by
        simp [mul_pow]

  /-
  Step 15: Replace `((n : ZMod p)^(p/2))` by `χ₈(n)` using Step 11.
  -/
  have hchi_pow : (ZMod.χ₈ n : ZMod p) = (2 : ZMod p) ^ k * f ^ k := by
    /-
    Step 15.1: First, rewrite the Euler-criterion identity so it uses the *nat* cast of `n`.

    This avoids a later type mismatch between `((n : ℤ) : ZMod p)` and `((n : ℕ) : ZMod p)`.
    -/
    have hcast_n : ((n : ℤ) : ZMod p) = ((n : ℕ) : ZMod p) := by
      norm_cast
    have hn_euler' : ((n : ℕ) : ZMod p) ^ (p / 2) = (ZMod.χ₈ n : ZMod p) := by
      simpa [hcast_n] using hn_euler

    /-
    Step 15.2: Combine Step 11 and Step 14.

    - Step 11: `n^(p/2) = χ₈(n)`.
    - Step 14: `n^(p/2) = 2^k * f^k`.

    Hence `χ₈(n) = 2^k * f^k`.
    -/
    calc
      (ZMod.χ₈ n : ZMod p) = ((n : ℕ) : ZMod p) ^ (p / 2) := by
        simpa using hn_euler'.symm
      _ = (2 : ZMod p) ^ k * f ^ k := hn_pow_calc

  /-
  Step 16: Rewrite `χ₈(n)` as a power of `f`.

  Textbook formula: `χ₈(n) = (-1)^((n^2-1)/8)`.
  Since `f^2 = -1`, we can rewrite this as
  `χ₈(n) = f^((n^2-1)/4)`.
  -/
  have hchi_as_f : (ZMod.χ₈ n : ZMod p) = f ^ ((n ^ 2 - 1) / 4) := by
    -- Step 16.1: rewrite `χ₈(n)` as a power of `-1` in ℤ, then cast to `ZMod p`.
    have hchi_int : (ZMod.χ₈ n : ZMod p) = (-1 : ZMod p) ^ ((n ^ 2 - 1) / 8) := by
      have hχ := chi8_eq_neg_one_pow_sq_sub_one_div_eight (n := n) hn_odd
      have hχ' := congrArg (fun z : ℤ => (z : ZMod p)) hχ
      simpa using hχ'
    -- Step 16.2: replace `-1` by `f^2` and combine exponents.
    have h8 : 8 ∣ n ^ 2 - 1 := Nat.eight_dvd_sq_sub_one_of_odd hn_odd
    rcases h8 with ⟨t, ht⟩
    -- With `n^2-1 = 8*t`, the exponents satisfy `(n^2-1)/8 = t` and `(n^2-1)/4 = 2*t`.
    have ht8 : (n ^ 2 - 1) / 8 = t := by
      -- divide both sides of `ht` by `8`
      simp [ht, (Nat.mul_div_right t (by norm_num : 0 < (8 : ℕ)))]
    have ht4 : (n ^ 2 - 1) / 4 = 2 * t := by
      /-
      Step 16.2.2: From `n^2 - 1 = 8*t`, compute the `/4` version:
      `(n^2-1)/4 = (8*t)/4 = 2*t`.

      We rewrite `8*t` as `4*(2*t)` and then cancel `/4`.
      -/
      calc
        (n ^ 2 - 1) / 4 = (8 * t) / 4 := by
          simp [ht]
        _ = (4 * (2 * t)) / 4 := by
          ring_nf
        _ = 2 * t := by
          simp [(Nat.mul_div_right (n := 2 * t) (m := 4) (by norm_num : 0 < (4 : ℕ)))]
    -- Now compute.
    calc
      (ZMod.χ₈ n : ZMod p) = (-1 : ZMod p) ^ ((n ^ 2 - 1) / 8) := hchi_int
      _ = (f ^ 2) ^ ((n ^ 2 - 1) / 8) := by
        simp [hf_sq]
      _ = f ^ (2 * ((n ^ 2 - 1) / 8)) := by
        -- `f^(2*m) = (f^2)^m`
        exact (pow_mul f 2 ((n ^ 2 - 1) / 8)).symm
      _ = f ^ ((n ^ 2 - 1) / 4) := by
        -- replace the exponent using `ht`.
        -- Both sides are `f^(2*t)`.
        -- We use the helper equalities `ht8` and `ht4`.
        simp [ht8, ht4]

  /-
  Step 17: Split the exponent `(n^2-1)/4` as `k + a*b/2`.

  This is a straightforward algebraic computation using `(a+b)^2 = p + 2ab`.
  -/
  have hexp_split : ((n ^ 2 - 1) / 4) = k + (a * b / 2) := by
    -- Expand `n = a+b`.
    have hn_sq : n ^ 2 = p + 2 * a * b := by
      -- `(a+b)^2 = a^2 + 2ab + b^2 = p + 2ab`.
      calc
        n ^ 2 = (a + b) ^ 2 := by simp [n]
        _ = a ^ 2 + 2 * a * b + b ^ 2 := by
          ring
        _ = (a ^ 2 + b ^ 2) + 2 * a * b := by
          ring
        _ = p + 2 * a * b := by
          simp [hab]
    -- Now subtract `1` and divide by `4`.
    calc
      (n ^ 2 - 1) / 4 = ((p + 2 * a * b) - 1) / 4 := by
        simp [hn_sq]
      _ = ((p - 1) + 2 * a * b) / 4 := by
        -- Move the `-1` inside the `p` term.
        -- We use `Nat.add_sub_assoc` with `1 ≤ p`.
        have : (p + 2 * a * b) - 1 = (2 * a * b) + (p - 1) := by
          -- reorder the sum and apply `Nat.add_sub_assoc`.
          calc
            (p + 2 * a * b) - 1 = (2 * a * b + p) - 1 := by
              simp [add_comm]
            _ = (2 * a * b) + (p - 1) := by
              simp [(Nat.add_sub_assoc (m := p) (k := 1) (h := hp_ge1) (n := 2 * a * b))]
        simp [this, add_comm]
      _ = (p - 1) / 4 + (2 * a * b) / 4 := by
        -- Divide a sum where the first term is divisible by `4`.
        simpa [add_comm, add_left_comm, add_assoc] using
          (Nat.add_div_of_dvd_right (b := 2 * a * b) hp_dvd4)
      _ = k + (a * b / 2) := by
        -- Simplify the second fraction: `(2ab)/4 = (ab)/2`.
        have : (2 * a * b) / 4 = (a * b) / 2 := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            (Nat.mul_div_mul_left (m := 2) (n := a * b) (k := 2) (by decide : 0 < (2 : ℕ)))
        simp [k, this, Nat.add_comm]

  /-
  Step 18: Combine Step 15, Step 16, and Step 17, and finally cancel `f^k`.
  -/
  have hchi_expanded : (ZMod.χ₈ n : ZMod p) = f ^ k * f ^ (a * b / 2) := by
    -- Use `χ₈(n) = f^((n^2-1)/4)` and split the exponent.
    calc
      (ZMod.χ₈ n : ZMod p) = f ^ ((n ^ 2 - 1) / 4) := hchi_as_f
      _ = f ^ (k + (a * b / 2)) := by
        simp [hexp_split]
      _ = f ^ k * f ^ (a * b / 2) := by
        simp [pow_add]

  -- Put the two expressions for `χ₈(n)` together.
  have hmain : (2 : ZMod p) ^ k * f ^ k = f ^ k * f ^ (a * b / 2) := by
    -- both sides equal `χ₈(n)`
    exact (hchi_pow.symm.trans hchi_expanded)

  -- Cancel `f^k` (which is nonzero because `f^2 = -1`).
  have hf_ne0 : f ≠ 0 := by
    intro hf0
    -- then `f^2 = 0`, contradicting `f^2 = -1`.
    have h1 : (f ^ 2 : ZMod p) = 0 := by simp [hf0]
    have h2 : (0 : ZMod p) = (-1 : ZMod p) := h1.symm.trans hf_sq
    simp at h2
  have hfk_ne0 : f ^ k ≠ 0 := pow_ne_zero k hf_ne0

  -- Multiply both sides of `hmain` by `(f^k)⁻¹` and simplify.
  have h' := congrArg (fun z : ZMod p => z * (f ^ k)⁻¹) hmain
  have rhs_simp : (f ^ k * f ^ (a * b / 2)) * (f ^ k)⁻¹ = f ^ (a * b / 2) := by
    calc
      (f ^ k * f ^ (a * b / 2)) * (f ^ k)⁻¹ = (f ^ (a * b / 2)) * (f ^ k * (f ^ k)⁻¹) := by
        -- rearrange the four factors using commutativity
        simp [mul_assoc, mul_comm]
      _ = f ^ (a * b / 2) := by
        simp [hfk_ne0]

  -- Finish the cancellation.
  have : (2 : ZMod p) ^ k = f ^ (a * b / 2) := by
    have : (2 : ZMod p) ^ k = (f ^ k * f ^ (a * b / 2)) * (f ^ k)⁻¹ := by
      -- simplify the left side of `h'`
      simpa [mul_assoc, mul_left_comm, mul_comm, hfk_ne0] using h'
    exact this.trans rhs_simp

  -- Finally rewrite `f` back to its definition.
  simpa [f, k]


theorem Ireland_Rosen_exercise_5_28 {p : ℕ} (hp : p.Prime) (hp1 : p ≡ 1 [MOD 4]) :
    (∃ x, x ^ 4 ≡ 2 [MOD p]) ↔ ∃ A B, p = A ^ 2 + 64 * B ^ 2 := by
  classical

  /-
  Step 0: Basic facts about `p`.
  -/
  have hp4 : p % 4 = 1 := by simpa using hp1
  have hp_ne2 : p ≠ 2 := by
    intro hp2
    subst hp2
    /-
    Step 0.1: If `p = 2` then `p % 4 = 2`, contradicting `hp4 : p % 4 = 1`.

    As above, we let `decide` prove the inequality `2 % 4 ≠ 1` and then apply it.
    -/
    have : (2 % 4 : ℕ) ≠ 1 := by decide
    exact this hp4
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (2 < p) := ⟨lt_of_le_of_ne (hp.two_le) (Ne.symm hp_ne2)⟩

  /-
  Step 1: Show `4 ∣ p-1` (we will use it repeatedly).
  -/
  have hp_ge1 : 1 ≤ p := Nat.succ_le_iff.mpr (hp.pos)
  have hp_dvd4 : 4 ∣ p - 1 := by
    have hsub : p - 1 ≡ 0 [MOD 4] := by
      simpa using (Nat.ModEq.sub (n := 4) (a := p) (b := 1) (c := 1) (d := 1)
        hp_ge1 (by decide) hp1 Nat.ModEq.rfl)
    have : (p - 1) % 4 = 0 := by simpa using hsub
    exact (Nat.dvd_iff_mod_eq_zero).2 this

  /-
  Step 2: Define the exponent `k = (p-1)/4`.
  -/
  set k : ℕ := (p - 1) / 4

  /-
  Step 3: Show that `(2 : ZMod p) ≠ 0`.
  -/
  have h2ne0 : (2 : ZMod p) ≠ 0 := by
    intro h2z
    have hp2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h2z
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2
    exact hp_ne2 this

  /-
  Step 4: The forward direction.

  Assume there is a solution to `x^4 ≡ 2 (mod p)`. We will show that `p = A^2 + 64 B^2`.
  -/
  constructor
  · rintro ⟨x, hx⟩

    /-
    Step 4.1: Convert the congruence into an equality in `ZMod p`.
    -/
    have hxZ : ((x : ZMod p) ^ 4) = (2 : ZMod p) := by
      -- `ZMod.natCast_eq_natCast_iff` converts between equality in `ZMod` and `Nat.ModEq`.
      have : ((x ^ 4 : ℕ) : ZMod p) = (2 : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff (x ^ 4) 2 p).2 hx
      simpa using this

    /-
    Step 4.2: Deduce `2^k = 1` in `ZMod p`.

    This is the easy direction: if `y^4 = 2`, then raising both sides to the power `k`
    yields `y^(p-1) = 2^k`. By Fermat's little theorem, `y^(p-1) = 1`.
    -/
    have hx_ne0 : (x : ZMod p) ≠ 0 := by
      intro hx0
      have : (2 : ZMod p) = 0 := by
        -- Use the *symmetric* form `2 = x^4` so that rewriting `x = 0` gives `2 = 0`.
        simpa [hx0] using hxZ.symm
      exact h2ne0 this

    have h4k : 4 * k = p - 1 := by
      -- `4 * ((p-1)/4) = p-1` because `4 ∣ p-1`.
      simpa [k] using (Nat.mul_div_cancel' hp_dvd4)

    have h2k : (2 : ZMod p) ^ k = 1 := by
      calc
        (2 : ZMod p) ^ k = ((x : ZMod p) ^ 4) ^ k := by
          simp [hxZ]
        _ = (x : ZMod p) ^ (4 * k) := by
          simp [pow_mul]
        _ = (x : ZMod p) ^ (p - 1) := by
          simp [h4k]
        _ = 1 := by
          simpa using (ZMod.pow_card_sub_one_eq_one (p := p) hx_ne0)

    /-
    Step 4.3: Represent `p` as a sum of two squares with an odd first component.
    -/
    have hp_mod4_ne3 : p % 4 ≠ 3 := by
      intro h3
      /-
      Step 4.3.1: Rewrite the assumption `p % 4 = 3` using `hp4 : p % 4 = 1`.

      This produces an absurd equality `1 = 3`, and we finish by applying the decidable fact
      `1 ≠ 3`.
      -/
      have hne : (1 : ℕ) ≠ 3 := by decide
      exact hne (hp4.symm.trans h3)
    obtain ⟨a0, b0, hab0⟩ := Nat.Prime.sq_add_sq (p := p) (hp := hp_mod4_ne3)

    -- Choose `a` to be the odd one among `{a0,b0}`.
    by_cases ha0 : Odd a0
    · -- Case 4.3.1: `a0` is odd.
      have hab : a0 ^ 2 + b0 ^ 2 = p := hab0
      have hEx :
          (2 : ZMod p) ^ ((p - 1) / 4) = ((b0 : ZMod p) * (a0 : ZMod p)⁻¹) ^ (a0 * b0 / 2) :=
        two_pow_sub_one_div_four_eq_f_pow_mul_div_two (p := p) (a := a0) (b := b0) hp hp1 hab ha0

      -- From `2^k = 1`, we get the corresponding power of `f` is also `1`.
      have hf_pow : ((b0 : ZMod p) * (a0 : ZMod p)⁻¹) ^ (a0 * b0 / 2) = 1 := by
        calc
          ((b0 : ZMod p) * (a0 : ZMod p)⁻¹) ^ (a0 * b0 / 2)
              = (2 : ZMod p) ^ ((p - 1) / 4) := by
                  simp [hEx]
          _ = 1 := by
            simpa [k] using h2k

      /-
      Step 4.4: Use `f^2 = -1` to conclude `4 ∣ a0*b0/2`, hence `8 ∣ b0`.
      -/
      have hneg1_ne1 : (-1 : ZMod p) ≠ 1 := ZMod.neg_one_ne_one
      -- Let `f` be the same element as in Ex. 5.27.
      let f : ZMod p := (b0 : ZMod p) * (a0 : ZMod p)⁻¹
      have hf_sq : f ^ 2 = (-1 : ZMod p) := by
        -- We can reuse the proof that is implicit in Ex. 5.27 by re-running its argument:
        -- it always produces `f^2 = -1`.
        -- Here we just compute directly from the equation `a0^2 + b0^2 = p`.
        have haZ : (a0 : ZMod p) ≠ 0 := by
          -- `a0 < p` because `a0^2 ≤ p`.
          have ha_sq_le : a0 ^ 2 ≤ p := by
            have : a0 ^ 2 ≤ a0 ^ 2 + b0 ^ 2 := Nat.le_add_right _ _
            simpa [hab] using this
          have ha_lt_p : a0 < p := by
            by_contra h
            have hpa : p ≤ a0 := Nat.le_of_not_gt h
            have hp2_le : p ^ 2 ≤ a0 ^ 2 := Nat.pow_le_pow_left hpa 2
            have : p ^ 2 ≤ p := le_trans hp2_le ha_sq_le
            have hp_lt_hp2 : p < p ^ 2 := by
              have hmul : p * 1 < p * p :=
                (Nat.mul_lt_mul_left (a := p) (b := 1) (c := p) hp.pos).2 hp.one_lt
              simpa [pow_two] using hmul
            exact (not_le_of_gt hp_lt_hp2) this
          intro ha0z
          have hp_dvd_a0 : p ∣ a0 := (ZMod.natCast_eq_zero_iff a0 p).1 ha0z
          have : a0 = 0 := Nat.eq_zero_of_dvd_of_lt hp_dvd_a0 ha_lt_p
          exact (ha0.pos.ne') this
        have habZ : (a0 : ZMod p) ^ 2 + (b0 : ZMod p) ^ 2 = 0 := by
          have : ((a0 ^ 2 + b0 ^ 2 : ℕ) : ZMod p) = (p : ZMod p) := congrArg (fun t : ℕ => (t : ZMod p)) hab
          simpa using (this.trans (ZMod.natCast_self p))
        have hb_sq : (b0 : ZMod p) ^ 2 = - (a0 : ZMod p) ^ 2 :=
          eq_neg_of_add_eq_zero_right habZ
        have ha_inv_sq : (a0 : ZMod p) ^ 2 * ((a0 : ZMod p)⁻¹) ^ 2 = 1 := by
          calc
            (a0 : ZMod p) ^ 2 * ((a0 : ZMod p)⁻¹) ^ 2
                = ((a0 : ZMod p) * (a0 : ZMod p)⁻¹) ^ 2 := by
                    simp [mul_pow]
            _ = 1 := by simp [haZ]
        -- Now compute `f^2`.
        calc
          f ^ 2 = (b0 : ZMod p) ^ 2 * ((a0 : ZMod p)⁻¹) ^ 2 := by
            simp [f, mul_pow]
          _ = (- (a0 : ZMod p) ^ 2) * ((a0 : ZMod p)⁻¹) ^ 2 := by
            simp [hb_sq]
          _ = - ((a0 : ZMod p) ^ 2 * ((a0 : ZMod p)⁻¹) ^ 2) := by
            ring
          _ = (-1 : ZMod p) := by
            /-
            As in the auxiliary lemma, `simp` at this point wants to cancel the inverse of `a0^2`.
            We therefore provide the fact `a0^2 ≠ 0`, which follows from `haZ : a0 ≠ 0`.
            -/
            have ha0sq_ne0 : (a0 : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 haZ
            simp [ha0sq_ne0]

      -- Show `4 ∣ a0*b0/2` via the “order 4” parity argument.
      set t : ℕ := a0 * b0 / 2

      /-
      Step 4.4.0: Rewrite `hf_pow` in terms of our local names `f` and `t`.

      This gives the clean statement `f^t = 1` that we can reuse below.
      -/
      have hf_pow_t : f ^ t = 1 := by
        simpa [f, t] using hf_pow

      have ht_even : Even t := by
        /-
        Step 4.4.1: From `f^t = 1` and `f^2 = -1`, deduce `(-1)^t = 1`.

        Indeed:
        `(f^2)^t = f^(2*t) = (f^t)^2 = 1`.
        -/
        have hneg : (-1 : ZMod p) ^ t = 1 := by
          calc
            (-1 : ZMod p) ^ t = (f ^ 2) ^ t := by
              simp [hf_sq]
            _ = f ^ (2 * t) := by
              -- `(f^2)^t = f^(2*t)`
              exact (pow_mul f 2 t).symm
            _ = (f ^ t) ^ 2 := by
              -- `f^(2*t) = (f^t)^2`
              rw [show 2 * t = t * 2 from Nat.mul_comm 2 t, pow_mul]
            _ = 1 := by
              -- because `f^t = 1`
              simp [hf_pow_t]

        /-
        Step 4.4.2: If `t` were odd, then `(-1)^t = -1`, contradicting Step 4.4.1.
        Hence `t` is even.
        -/
        by_contra htne
        have htodd : Odd t := (Nat.not_even_iff_odd).1 htne
        have hneg' : (-1 : ZMod p) ^ t = (-1 : ZMod p) := by
          simpa using htodd.neg_one_pow
        exact hneg1_ne1 (by
          calc
            (-1 : ZMod p) = (-1 : ZMod p) ^ t := by
              simpa using hneg'.symm
            _ = 1 := hneg)

      -- From `t` even, we get `t = 2*u`; then `(-1)^u = 1` forces `u` even; hence `4 ∣ t`.
      have ht4 : 4 ∣ t := by
        rcases ht_even with ⟨u, hu⟩
        have ht2 : t = 2 * u := by simpa [two_mul] using hu
        -- From `f^t = 1` and `t = 2*u`, we get `(-1)^u = 1`.
        have hneg_u : (-1 : ZMod p) ^ u = 1 := by
          have : f ^ (2 * u) = 1 := by
            -- Rewrite `f^t = 1` using `t = 2*u`.
            simpa [ht2] using hf_pow_t
          -- `f^(2*u) = (f^2)^u = (-1)^u`.
          simpa [pow_mul, hf_sq] using this
        -- Hence `u` is even.
        have hu_even : Even u := by
          by_contra hune
          have hu_odd : Odd u := (Nat.not_even_iff_odd).1 hune
          have hneg_u' : (-1 : ZMod p) ^ u = (-1 : ZMod p) := by
            simpa using hu_odd.neg_one_pow
          exact hneg1_ne1 (by
            calc
              (-1 : ZMod p) = (-1 : ZMod p) ^ u := by
                simpa using hneg_u'.symm
              _ = 1 := hneg_u)
        rcases hu_even with ⟨v, hv⟩
        have hu2 : u = 2 * v := by simpa [two_mul] using hv
        refine ⟨v, ?_⟩
        -- `t = 2*u = 4*v`.
        calc
          t = 2 * u := ht2
          _ = 2 * (2 * v) := by
            simp [hu2]
          _ = 4 * v := by
            ring

      /-
      Step 4.5: Turn `4 ∣ a0*b0/2` into `8 ∣ b0`.
      -/
      have hb_even : Even b0 := by
        -- Since `p` is odd and `a0` is odd, `b0` must be even.
        have hp_odd : Odd p := by
          exact (Nat.odd_iff).2 (Nat.odd_of_mod_four_eq_one hp4)
        have ha2_odd : Odd (a0 ^ 2) := by
          simpa using (ha0.pow (n := 2))
        have hsum_odd : Odd (a0 ^ 2 + b0 ^ 2) := by simpa [hab] using hp_odd
        have hb2_even : Even (b0 ^ 2) := ((Nat.odd_add).1 hsum_odd).1 ha2_odd
        exact (Nat.even_pow).1 hb2_even |>.1

      have ha_coprime4 : Nat.Coprime a0 4 := by
        -- `a0` odd ⇒ `a0` coprime to `2`, hence coprime to `4 = 2*2`.
        have h2 : Nat.Coprime a0 2 := (Nat.coprime_two_right).2 ha0
        simpa using h2.mul_right h2

      -- Rewrite `t = a0*b0/2` as `a0*(b0/2)` using the evenness of `b0`.
      rcases hb_even with ⟨c, hc⟩
      have hb0_two : b0 = 2 * c := by simpa [two_mul] using hc
      have ht : t = a0 * c := by
        /-
        Step 4.5.1: Rewrite `t = a0*b0/2` using `b0 = 2*c`.

        Then rearrange the multiplication so that we can cancel the `/2`.
        -/
        have hmul : a0 * (2 * c) = 2 * (a0 * c) := by
          ring
        calc
          t = a0 * b0 / 2 := by
            rfl
          _ = a0 * (2 * c) / 2 := by
            simp [hb0_two]
          _ = (2 * (a0 * c)) / 2 := by
            simp [hmul]
          _ = a0 * c := by
            -- `2*(a0*c)/2 = a0*c`
            simp [(Nat.mul_div_right (n := a0 * c) (m := 2) (by norm_num : 0 < (2 : ℕ)))]

      have h4div_ac : 4 ∣ a0 * c := by simp [ht] at ht4; exact ht4
      -- Since `4` is coprime to `a0`, `4 ∣ c`.
      have h4div_c : 4 ∣ c := by
        have : Nat.Coprime 4 a0 := ha_coprime4.symm
        exact (this.dvd_mul_left).1 h4div_ac
      -- Hence `8 ∣ b0 = 2*c`.
      have h8div_b0 : 8 ∣ b0 := by
        rcases h4div_c with ⟨d, hd⟩
        refine ⟨d, ?_⟩
        -- `b0 = 2*c = 2*(4*d) = 8*d`.
        simp [hb0_two, hd, Nat.mul_left_comm, Nat.mul_comm]

      -- Finally, package `p = a0^2 + 64*B^2`.
      rcases h8div_b0 with ⟨B, hB⟩
      refine ⟨a0, B, ?_⟩
      -- Use `p = a0^2 + b0^2` and rewrite `b0 = 8*B`.
      calc
        p = a0 ^ 2 + b0 ^ 2 := by
          simp [hab]
        _ = a0 ^ 2 + (8 * B) ^ 2 := by
          simp [hB]
        _ = a0 ^ 2 + 64 * B ^ 2 := by
          ring

    · -- Case 4.3.2: `a0` is even, so `b0` is odd; swap roles.
      have ha0_even : Even a0 := (Nat.not_odd_iff_even).1 ha0
      have hb0_odd : Odd b0 := by
        -- `p` is odd and `a0^2` is even, so `b0^2` is odd, hence `b0` is odd.
        have hp_odd : Odd p := by
          exact (Nat.odd_iff).2 (Nat.odd_of_mod_four_eq_one hp4)
        have hsum_odd : Odd (a0 ^ 2 + b0 ^ 2) := by simpa [hab0] using hp_odd
        have ha0sq_even : Even (a0 ^ 2) := by
          simpa [pow_two] using ha0_even.mul_right a0
        -- If `b0^2` were even, the sum would be even, contradiction.
        have hb0sq_not_even : ¬Even (b0 ^ 2) := by
          intro hb0sq_even
          have : Even (a0 ^ 2 + b0 ^ 2) := ha0sq_even.add hb0sq_even
          exact (Nat.not_even_iff_odd).2 hsum_odd this
        -- `b0^2` not even ⇒ `b0` not even ⇒ `b0` odd.
        have hb0_not_even : ¬Even b0 := by
          intro hb0_even
          have : Even (b0 ^ 2) := by
            simpa [pow_two] using hb0_even.mul_right b0
          exact hb0sq_not_even this
        exact (Nat.not_even_iff_odd).1 hb0_not_even

      -- Now apply the odd case with `a = b0`, `b = a0`.
      have hab : b0 ^ 2 + a0 ^ 2 = p := by simpa [add_comm] using hab0
      have hEx :
          (2 : ZMod p) ^ ((p - 1) / 4) = ((a0 : ZMod p) * (b0 : ZMod p)⁻¹) ^ (b0 * a0 / 2) :=
        two_pow_sub_one_div_four_eq_f_pow_mul_div_two (p := p) (a := b0) (b := a0) hp hp1 hab hb0_odd

      have hf_pow : ((a0 : ZMod p) * (b0 : ZMod p)⁻¹) ^ (b0 * a0 / 2) = 1 := by
        calc
          ((a0 : ZMod p) * (b0 : ZMod p)⁻¹) ^ (b0 * a0 / 2)
              = (2 : ZMod p) ^ ((p - 1) / 4) := by
                  simp [hEx]
          _ = 1 := by
            simpa [k] using h2k

      /-
      Step 4.4 (swapped version): Repeat the same argument as in Case 4.3.1,
      but with roles swapped: now `a = b0` is odd and `b = a0` is even.

      We will show `8 ∣ a0`, and hence `p = b0^2 + 64*B^2`.
      -/

      /-
      Step 4.4.1: Let `f = a0 / b0` in `ZMod p`.
      -/
      let f : ZMod p := (a0 : ZMod p) * (b0 : ZMod p)⁻¹

      /-
      Step 4.4.2: Prove `f^2 = -1`.

      This is the same computation as before, using the relation
      `a0^2 + b0^2 = p` inside `ZMod p`.
      -/
      have hb0_sq_le : b0 ^ 2 ≤ p := by
        have : b0 ^ 2 ≤ a0 ^ 2 + b0 ^ 2 := Nat.le_add_left _ _
        -- rewrite `a0^2 + b0^2` as `p`
        simpa [hab0] using this

      have hb0_lt_p : b0 < p := by
        -- Same “square growth” argument as earlier.
        by_contra h
        have hpb0 : p ≤ b0 := Nat.le_of_not_gt h
        have hp2_le : p ^ 2 ≤ b0 ^ 2 := Nat.pow_le_pow_left hpb0 2
        have : p ^ 2 ≤ p := le_trans hp2_le hb0_sq_le
        have hp_lt_hp2 : p < p ^ 2 := by
          have hmul : p * 1 < p * p :=
            (Nat.mul_lt_mul_left (a := p) (b := 1) (c := p) hp.pos).2 hp.one_lt
          simpa [pow_two] using hmul
        exact (not_le_of_gt hp_lt_hp2) this

      have hb0Z : (b0 : ZMod p) ≠ 0 := by
        intro hb0z
        have hp_dvd_b0 : p ∣ b0 := (ZMod.natCast_eq_zero_iff b0 p).1 hb0z
        have : b0 = 0 := Nat.eq_zero_of_dvd_of_lt hp_dvd_b0 hb0_lt_p
        exact (hb0_odd.pos.ne') this

      have hf_sq : f ^ 2 = (-1 : ZMod p) := by
        -- Cast `a0^2 + b0^2 = p` to `ZMod p`.
        have habZ : (a0 : ZMod p) ^ 2 + (b0 : ZMod p) ^ 2 = 0 := by
          have : ((a0 ^ 2 + b0 ^ 2 : ℕ) : ZMod p) = (p : ZMod p) :=
            congrArg (fun t : ℕ => (t : ZMod p)) hab0
          simpa using (this.trans (ZMod.natCast_self p))

        -- From `a0^2 + b0^2 = 0`, get `a0^2 = -b0^2`.
        have ha_sq : (a0 : ZMod p) ^ 2 = - (b0 : ZMod p) ^ 2 :=
          eq_neg_of_add_eq_zero_left (by simpa [add_comm] using habZ)

        -- Now compute `f^2 = (a0/b0)^2`.
        have hb0sq_ne0 : (b0 : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 hb0Z
        calc
          f ^ 2 = (a0 : ZMod p) ^ 2 * ((b0 : ZMod p)⁻¹) ^ 2 := by
            simp [f, mul_pow]
          _ = (- (b0 : ZMod p) ^ 2) * ((b0 : ZMod p)⁻¹) ^ 2 := by
            simp [ha_sq]
          _ = - ((b0 : ZMod p) ^ 2 * ((b0 : ZMod p)⁻¹) ^ 2) := by
            ring
          _ = (-1 : ZMod p) := by
            simp [hb0sq_ne0]

      /-
      Step 4.4.3: From `f^(b0*a0/2) = 1` and `f^2 = -1`, deduce `4 ∣ (b0*a0/2)`.
      -/
      set t : ℕ := b0 * a0 / 2
      have hf_pow_t : f ^ t = 1 := by
        simpa [f, t] using hf_pow

      -- We will repeatedly use that `-1 ≠ 1` in `ZMod p` (since `p > 2`).
      have hneg1_ne1 : (-1 : ZMod p) ≠ 1 := ZMod.neg_one_ne_one

      have ht4 : 4 ∣ t := by
        -- As before: first show `t` is even.
        have ht_even : Even t := by
          have hneg : (-1 : ZMod p) ^ t = 1 := by
            calc
              (-1 : ZMod p) ^ t = (f ^ 2) ^ t := by
                simp [hf_sq]
              _ = f ^ (2 * t) := by
                exact (pow_mul f 2 t).symm
              _ = (f ^ t) ^ 2 := by
                rw [show 2 * t = t * 2 from Nat.mul_comm 2 t, pow_mul]
              _ = 1 := by
                simp [hf_pow_t]
          by_contra htne
          have htodd : Odd t := (Nat.not_even_iff_odd).1 htne
          have hneg' : (-1 : ZMod p) ^ t = (-1 : ZMod p) := by
            simpa using htodd.neg_one_pow
          exact hneg1_ne1 (by
            calc
              (-1 : ZMod p) = (-1 : ZMod p) ^ t := by
                simpa using hneg'.symm
              _ = 1 := hneg)

        -- Now upgrade `Even t` to `4 ∣ t` exactly as in Case 4.3.1.
        rcases ht_even with ⟨u, hu⟩
        have ht2 : t = 2 * u := by simpa [two_mul] using hu
        have hneg_u : (-1 : ZMod p) ^ u = 1 := by
          have : f ^ (2 * u) = 1 := by
            simpa [ht2] using hf_pow_t
          simpa [pow_mul, hf_sq] using this
        have hu_even : Even u := by
          by_contra hune
          have hu_odd : Odd u := (Nat.not_even_iff_odd).1 hune
          have hneg_u' : (-1 : ZMod p) ^ u = (-1 : ZMod p) := by
            simpa using hu_odd.neg_one_pow
          exact hneg1_ne1 (by
            calc
              (-1 : ZMod p) = (-1 : ZMod p) ^ u := by
                simpa using hneg_u'.symm
              _ = 1 := hneg_u)
        rcases hu_even with ⟨v, hv⟩
        have hu2 : u = 2 * v := by simpa [two_mul] using hv
        refine ⟨v, ?_⟩
        calc
          t = 2 * u := ht2
          _ = 2 * (2 * v) := by
            simp [hu2]
          _ = 4 * v := by
            ring

      /-
      Step 4.4.4: Turn `4 ∣ (b0*a0/2)` into `8 ∣ a0`.
      -/
      have hb0_coprime4 : Nat.Coprime b0 4 := by
        have h2 : Nat.Coprime b0 2 := (Nat.coprime_two_right).2 hb0_odd
        simpa using h2.mul_right h2

      -- Rewrite `t = b0*a0/2` as `b0*(a0/2)` using the evenness of `a0`.
      rcases ha0_even with ⟨c, hc⟩
      have ha0_two : a0 = 2 * c := by
        simpa [two_mul] using hc
      have ht : t = b0 * c := by
        have hmul : b0 * (2 * c) = 2 * (b0 * c) := by
          ring
        calc
          t = b0 * a0 / 2 := by
            rfl
          _ = b0 * (2 * c) / 2 := by
            simp [ha0_two]
          _ = (2 * (b0 * c)) / 2 := by
            simp [hmul]
          _ = b0 * c := by
            simp [(Nat.mul_div_right (n := b0 * c) (m := 2) (by norm_num : 0 < (2 : ℕ)))]

      have h4div_bc : 4 ∣ b0 * c := by
        simp [ht] at ht4; exact ht4
      have h4div_c : 4 ∣ c := by
        have : Nat.Coprime 4 b0 := hb0_coprime4.symm
        exact (this.dvd_mul_left).1 h4div_bc
      have h8div_a0 : 8 ∣ a0 := by
        rcases h4div_c with ⟨d, hd⟩
        refine ⟨d, ?_⟩
        -- `a0 = 2*c = 2*(4*d) = 8*d`.
        simp [ha0_two, hd, Nat.mul_left_comm, Nat.mul_comm]

      /-
      Step 4.4.5: Package the final representation `p = b0^2 + 64*B^2`.
      -/
      rcases h8div_a0 with ⟨B, hB⟩
      refine ⟨b0, B, ?_⟩
      calc
        p = a0 ^ 2 + b0 ^ 2 := by
          simp [hab0]
        _ = b0 ^ 2 + a0 ^ 2 := by
          simp [add_comm]
        _ = b0 ^ 2 + (8 * B) ^ 2 := by
          simp [hB]
        _ = b0 ^ 2 + 64 * B ^ 2 := by
          ring

  /-
  Step 5: The reverse direction.

  Assume `p = A^2 + 64 B^2`. We show that `x^4 ≡ 2 (mod p)` has a solution.
  -/
  · rintro ⟨A, B, hAB⟩

    /-
    Step 5.1: Use Ex. 5.27 (the lemma above) with `a = A` and `b = 8*B`.
    -/
    have hp_odd : Odd p := by
      exact (Nat.odd_iff).2 (Nat.odd_of_mod_four_eq_one hp4)

    have hEven64 : Even (64 * B ^ 2) := by
      -- `64` is even.
      have : Even (64 : ℕ) := by decide
      exact this.mul_right _

    have hOddA2 : Odd (A ^ 2) := by
      -- From `p = A^2 + 64 B^2` and the fact that `64B^2` is even.
      have hsum_odd : Odd (A ^ 2 + 64 * B ^ 2) := by
        simpa [hAB] using hp_odd
      have hiff : Odd (A ^ 2) ↔ Even (64 * B ^ 2) := (Nat.odd_add).1 hsum_odd
      exact hiff.2 hEven64

    have hOddA : Odd A := by
      -- If `A` were even, then `A^2` would be even.
      have hnot_evenA2 : ¬Even (A ^ 2) := (Nat.not_even_iff_odd).2 hOddA2
      have hnot_evenA : ¬Even A := by
        intro hEvenA
        have : Even (A ^ 2) := by
          simpa [pow_two] using hEvenA.mul_right A
        exact hnot_evenA2 this
      exact (Nat.not_even_iff_odd).1 hnot_evenA

    -- Define `b = 8*B` so that `A^2 + b^2 = p`.
    set b : ℕ := 8 * B
    have hab : A ^ 2 + b ^ 2 = p := by
      -- Expand `b^2 = (8*B)^2 = 64*B^2`.
      have : b ^ 2 = 64 * B ^ 2 := by
        simp [b]; ring
      -- Rewrite `p` using `hAB`.
      simp [hAB, this]

    have hEx :
        (2 : ZMod p) ^ ((p - 1) / 4) = ((b : ZMod p) * (A : ZMod p)⁻¹) ^ (A * b / 2) :=
      two_pow_sub_one_div_four_eq_f_pow_mul_div_two (p := p) (a := A) (b := b) hp hp1 hab hOddA

    /-
    Step 5.1.1: Define the element `f = b/A` in `ZMod p`.
    -/
    let f : ZMod p := (b : ZMod p) * (A : ZMod p)⁻¹

    /-
    Step 5.1.2: Prove `f^2 = -1` (this will imply `f^4 = 1`).

    This is the same computation used earlier in the forward direction.
    -/
    have hA_sq_le : A ^ 2 ≤ p := by
      have : A ^ 2 ≤ A ^ 2 + b ^ 2 := Nat.le_add_right _ _
      simpa [hab] using this

    have hA_lt_p : A < p := by
      by_contra h
      have hpA : p ≤ A := Nat.le_of_not_gt h
      have hp2_le : p ^ 2 ≤ A ^ 2 := Nat.pow_le_pow_left hpA 2
      have : p ^ 2 ≤ p := le_trans hp2_le hA_sq_le
      have hp_lt_hp2 : p < p ^ 2 := by
        have hmul : p * 1 < p * p :=
          (Nat.mul_lt_mul_left (a := p) (b := 1) (c := p) hp.pos).2 hp.one_lt
        simpa [pow_two] using hmul
      exact (not_le_of_gt hp_lt_hp2) this

    have hAZ : (A : ZMod p) ≠ 0 := by
      intro hAz
      have hp_dvd_A : p ∣ A := (ZMod.natCast_eq_zero_iff A p).1 hAz
      have : A = 0 := Nat.eq_zero_of_dvd_of_lt hp_dvd_A hA_lt_p
      exact (hOddA.pos.ne') this

    have hf_sq : f ^ 2 = (-1 : ZMod p) := by
      -- Cast `A^2 + b^2 = p` to `ZMod p`.
      have habZ : (A : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
        have : ((A ^ 2 + b ^ 2 : ℕ) : ZMod p) = (p : ZMod p) :=
          congrArg (fun t : ℕ => (t : ZMod p)) hab
        simpa using (this.trans (ZMod.natCast_self p))

      have hb_sq : (b : ZMod p) ^ 2 = - (A : ZMod p) ^ 2 :=
        eq_neg_of_add_eq_zero_right habZ

      have hAsq_ne0 : (A : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 hAZ
      calc
        f ^ 2 = (b : ZMod p) ^ 2 * ((A : ZMod p)⁻¹) ^ 2 := by
          simp [f, mul_pow]
        _ = (- (A : ZMod p) ^ 2) * ((A : ZMod p)⁻¹) ^ 2 := by
          simp [hb_sq]
        _ = - ((A : ZMod p) ^ 2 * ((A : ZMod p)⁻¹) ^ 2) := by
          ring
        _ = (-1 : ZMod p) := by
          simp [hAsq_ne0]

    /-
    Step 5.2: The exponent `A*b/2` is a multiple of `4` because `b = 8*B`.
    Hence `f^(A*b/2) = 1`, and therefore `2^k = 1`.
    -/
    have hb_mul : A * b / 2 = 4 * (A * B) := by
      /-
      Step 5.2.1: Rewrite `A*b/2` using `b = 8*B` and then cancel the `/2` explicitly.

      We show
      `A*b = 2 * (4 * (A*B))`,
      and then use `Nat.mul_div_right` to cancel.
      -/
      have hmul : A * b = 2 * (4 * (A * B)) := by
        -- Expand `b = 8*B` and normalize products.
        simp [b, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      calc
        A * b / 2 = (2 * (4 * (A * B))) / 2 := by
          simp [hmul]
        _ = 4 * (A * B) := by
          simp [(Nat.mul_div_right (n := 4 * (A * B)) (m := 2) (by norm_num : 0 < (2 : ℕ)))]

    have h2k : (2 : ZMod p) ^ ((p - 1) / 4) = 1 := by
      /-
      Step 5.2.2: Use Ex. 5.27 to rewrite `2^k` as `f^(A*b/2)`.
      Then use `A*b/2 = 4*(A*B)` and the fact `f^4 = 1`.
      -/
      have hf4 : f ^ 4 = 1 := by
        -- `f^4 = (f^2)^2 = (-1)^2 = 1`.
        calc
          f ^ 4 = (f ^ 2) ^ 2 := by
            simp [(pow_mul f 2 2)]
          _ = (-1 : ZMod p) ^ 2 := by
            simp [hf_sq]
          _ = 1 := by
            simp

      calc
        (2 : ZMod p) ^ ((p - 1) / 4) = f ^ (A * b / 2) := by
          simp [f, hEx]
        _ = f ^ (4 * (A * B)) := by
          simp [hb_mul]
        _ = 1 := by
          -- `f^(4*n) = (f^4)^n = 1`.
          calc
            f ^ (4 * (A * B)) = (f ^ 4) ^ (A * B) := by
              simp [pow_mul, (pow_mul f 4 (A * B))]
            _ = 1 := by
              simp [hf4]

    /-
    Step 5.3: Use the cyclicity of `(ZMod p)ˣ` to extract a fourth root of `2`.
    -/
    haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp

    let u2 : (ZMod p)ˣ := Units.mk0 (2 : ZMod p) h2ne0
    have hu2k : u2 ^ ((p - 1) / 4) = 1 := by
      -- Compare values in `ZMod p`.
      apply Units.ext
      -- Use `Units.val_pow_eq_pow_val`.
      simp [u2, Units.val_pow_eq_pow_val, h2k]

    have hcard : 4 ∣ Nat.card (ZMod p)ˣ := by
      /-
      Step 5.3.1: Rewrite `Nat.card (ZMod p)ˣ` as `p.totient`.

      This is the most simp-friendly normal form for the cardinality of the unit group.
      -/
      have hcard_eq : Nat.card (ZMod p)ˣ = p.totient := by
        classical
        simp [Nat.card_eq_fintype_card, (ZMod.card_units_eq_totient (n := p))]

      /-
      Step 5.3.2: For a prime `p`, we have `p.totient = p - 1`, so `4 ∣ p.totient`.
      -/
      have : 4 ∣ p.totient := by
        simpa [Nat.totient_prime hp] using hp_dvd4

      /-
      Step 5.3.3: Transport the divisibility back along `hcard_eq`.
      -/
      simpa [hcard_eq] using this

    /-
    Step 5.3.4: Convert `u2^((p-1)/4) = 1` into the form expected by the cyclic-group lemma,
    namely `u2^(Nat.card (ZMod p)ˣ / 4) = 1`.
    -/
    have hu2k' : u2 ^ (Nat.card (ZMod p)ˣ / 4) = 1 := by
      have hcard_eq : Nat.card (ZMod p)ˣ = p.totient := by
        classical
        simp [Nat.card_eq_fintype_card, (ZMod.card_units_eq_totient (n := p))]
      -- Reduce to the already proven statement `hu2k` by rewriting `p.totient = p-1`.
      simpa [hcard_eq, Nat.totient_prime hp] using hu2k

    obtain ⟨u, hu⟩ :=
      exists_pow_four_eq_of_pow_card_div_four_eq_one (G := (ZMod p)ˣ) hcard hu2k'

    /-
    Step 5.4: Convert the unit solution into a natural-number solution.
    -/
    have hy : ((u : ZMod p) ^ 4) = (2 : ZMod p) := by
      -- Take values of the equation `u^4 = u2`.
      have := congrArg (fun w : (ZMod p)ˣ => (w : ZMod p)) hu
      simpa [u2, Units.val_pow_eq_pow_val] using this

    refine ⟨(u : ZMod p).val, ?_⟩
    -- Convert the equality in `ZMod p` back to a `Nat.ModEq` statement.
    have hy' : (((u : ZMod p).val : ZMod p) ^ 4) = (2 : ZMod p) := by
      -- Replace `(u : ZMod p)` by its canonical representative `val`.
      calc
        (((u : ZMod p).val : ZMod p) ^ 4) = (u : ZMod p) ^ 4 := by
          simp
        _ = (2 : ZMod p) := hy
    exact (ZMod.natCast_eq_natCast_iff ((u : ZMod p).val ^ 4) 2 p).1 (by exact_mod_cast hy')
