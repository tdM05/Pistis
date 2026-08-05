import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $a > 1$ is an integer, show that $n \mid \varphi(a^n - 1)$, where $\phi$ is the Euler $\varphi$-function.
-/

/-Informal Proof

Proof: We have $a>1$. First we propose to prove that
$$
\operatorname{Gcd}\left(a, a^n-1\right)=1 .
$$
If possible, let us assume that
$\operatorname{Gcd}\left(a, a^n-1\right)=d$, where $d>1$.
Then
$d$ divides $a$ as well as $a^n-1$.
Now,
$d$ divides $a \Longrightarrow d$ divides $a^n$.
This is an impossibility, since $d$ divides $a^n-1$ by our assumption. Consequently, $d$ divides 1 , which implies $d=1$. Hence we are contradict to the fact that $d>1$. Therefore
$$
\operatorname{Gcd}\left(a, a^n-1\right)=1 .
$$
Then $a \in U_{a^n-1}$, where $U_n$ is a group defined by
$$
U_n:=\left\{\bar{a} \in \mathbb{Z}_n \mid \operatorname{Gcd}(a, n)=1\right\} .
$$
We know that order of an element divides the order of the group. Here order of the group $U_{a^n-1}$ is $\phi\left(a^n-1\right)$ and $a \in U_{a^n-1}$. This follows that $\mathrm{o}(a)$ divides $\phi\left(a^n-1\right)$.
-/

theorem Herstein_exercise_2_4_36 {a n : ℕ} (h : a > 1) :
  n ∣ (a ^ n - 1).totient := by
  classical
  -- Step 1: Split into the cases `n = 0` and `n ≠ 0`.
  by_cases hn : n = 0
  · -- Step 1.1: If `n = 0`, all quantities collapse to zero and the divisibility is immediate.
    subst hn
    simp
  -- Step 2: Work under the standing assumption `n ≠ 0`, so `n` is positive.
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  -- Step 2.1: Introduce the modulus `m = a ^ n - 1` for the cyclic group argument.
  set m := a ^ n - 1 with hmdef
  -- Step 2.2: Record that `m` is positive because `a > 1` and `n > 0`.
  have ha_pos : 0 < a := lt_trans (Nat.zero_lt_one) h
  have hmpos : 0 < m := by
    -- Step 2.2.1: `a ^ n` strictly exceeds `1`, so the subtraction by `1` yields a positive number.
    have hpow_gt_one : 1 < a ^ n := Nat.one_lt_pow (n := n) (a := a) hn h
    exact Nat.sub_pos_of_lt hpow_gt_one
  -- Step 2.3: Show that `a` has order dividing `n` inside `ZMod m` by checking `a ^ n = 1`.
  have hpow_zmod : ((a : ZMod m) ^ n) = 1 := by
    -- Step 2.3.1: Rewrite the power using the `ℕ → ZMod` ring homomorphism.
    have hone_le : 1 ≤ a ^ n := Nat.one_le_pow n a ha_pos
    have hcalc :=
      congrArg (fun t : ℕ => (t : ZMod m)) (Nat.sub_add_cancel hone_le)
    have hmcast : ((m : ℕ) : ZMod m) = 0 := by
      simp [m]
    have hcast : ((a ^ n : ℕ) : ZMod m) = (1 : ZMod m) := by
      have hcalc' :
          ((a ^ n - 1 : ℕ) : ZMod m) + 1 = ((a ^ n : ℕ) : ZMod m) := by
        simpa using hcalc
      have hzero :
          ((a ^ n - 1 : ℕ) : ZMod m) = 0 := by
        have hcalc'' :
            ((a ^ n - 1 : ℕ) : ZMod m) + 1 = (1 : ZMod m) := by
          -- Step 2.3.1.1: Substitute the fact that `(a ^ n : ℕ)` reduces to `1`.
          simp
        -- Step 2.3.1.2: Subtract `1` on both sides to isolate the casted difference.
        have := congrArg (fun t : ZMod m => t - 1) hcalc''
        simp
      -- Step 2.3.1.3: Combine the facts to deduce that `a ^ n` maps to `1` in `ZMod m`.
      calc
        ((a ^ n : ℕ) : ZMod m)
            = ((a ^ n - 1 : ℕ) : ZMod m) + 1 := by
              simpa [Nat.cast_add, Nat.cast_one] using hcalc'.symm
        _ = 0 + 1 := by simp
        _ = 1 := by simp
    -- Step 2.3.2: Translate the previous computation back to the power of the class of `a`.
    simpa [Nat.cast_pow] using hcast
  -- Step 2.4: Exhibit the element of `(ZMod m)ˣ` represented by `a` together with its inverse.
  have hpow_succ :
      (a : ZMod m) ^ ((n - 1) + 1) = 1 := by
    -- Step 2.4.1: Re-express the exponent to match `pow_succ`.
    have hn_succ :
        (n - 1) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hnpos)
    simpa [hn_succ] using hpow_zmod
  have hmul_right :
      ((a : ZMod m) ^ (n - 1)) * (a : ZMod m) = 1 := by
    -- Step 2.4.2: Expand the `n`-th power using `pow_succ`.
    simpa [pow_succ] using hpow_succ
  have hmul_left :
      (a : ZMod m) * (a : ZMod m) ^ (n - 1) = 1 := by
    -- Step 2.4.3: Use commutativity to flip the factors.
    simpa [mul_comm] using hmul_right
  let u : Units (ZMod m) :=
    ⟨(a : ZMod m), (a : ZMod m) ^ (n - 1), hmul_left, hmul_right⟩
  -- Step 2.5: Prove that the order of `u` is exactly `n`.
  have hun_pow : u ^ n = 1 := by
    -- Step 2.5.1: Reduce to the equality already established inside `ZMod m`.
    ext
    simp [u, hpow_zmod]
  -- Step 2.5.2: Show that no smaller positive power of `u` can be equal to `1`.
  have hpow_ne :
      ∀ {k : ℕ}, k < n → 0 < k → u ^ k ≠ 1 := by
    -- Step 2.5.2.1: Assume towards a contradiction that a smaller positive power is `1`.
    intro k hklt hkpos hkunit
    -- Step 2.5.2.2: Translate the equality back to the ambient ring.
    have hval : ((a : ZMod m) ^ k) = 1 := by
      have := congrArg Units.val hkunit
      simpa [u] using this
    have hNatPowCast : ((a ^ k : ℕ) : ZMod m) = (1 : ZMod m) := by
      simpa [Nat.cast_pow] using hval
    -- Step 2.5.2.3: Infer that `m` divides `a ^ k - 1`.
    have hk_le : 1 ≤ a ^ k := Nat.one_le_pow k a ha_pos
    have hcalc :=
      congrArg (fun t : ℕ => (t : ZMod m)) (Nat.sub_add_cancel hk_le)
    have hcalc' :
        ((a ^ k - 1 : ℕ) : ZMod m) + 1 = ((a ^ k : ℕ) : ZMod m) := by
      simpa using hcalc
    have hzero :
        ((a ^ k - 1 : ℕ) : ZMod m) = 0 := by
      have hcalc'' :
          ((a ^ k - 1 : ℕ) : ZMod m) + 1 = (1 : ZMod m) := by
        simpa [hNatPowCast] using hcalc'
      have := congrArg (fun t : ZMod m => t - 1) hcalc''
      simpa using this
    have hdiv : m ∣ a ^ k - 1 :=
      (ZMod.natCast_eq_zero_iff (a ^ k - 1) m).1
        (by simpa using hzero)
    -- Step 2.5.2.4: Compare magnitudes to contradict the divisibility.
    have hpow_lt :
        a ^ k < a ^ n := (Nat.pow_lt_pow_iff_right h).2 hklt
    have hlt : a ^ k - 1 < m := by
      have hlt' :
          a ^ k - 1 < a ^ n - 1 :=
        Nat.sub_lt_sub_right (a := a ^ k) (b := a ^ n) (c := 1) hk_le hpow_lt
      simpa [m, hmdef] using hlt'
    have hk_ne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hkpos
    have hpos : 0 < a ^ k - 1 :=
      Nat.sub_pos_of_lt (Nat.one_lt_pow (n := k) (a := a) hk_ne h)
    have hm_le : m ≤ a ^ k - 1 := Nat.le_of_dvd hpos hdiv
    have : m < m := lt_of_le_of_lt hm_le hlt
    exact lt_irrefl _ this
  -- Step 2.5.2: Invoke the characterization of the order via minimal positive powers.
  have horder_eq : orderOf u = n := by
    refine (orderOf_eq_iff hnpos).2 ?_
    exact ⟨hun_pow, fun m hm_lt hm_pos => hpow_ne hm_lt hm_pos⟩
  -- Step 2.6: Apply Lagrange’s theorem to translate the order information into divisibility.
  haveI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  have horder_dvd :
      orderOf u ∣ Nat.totient m := by
    -- Step 2.6.1: Use the cardinality of `(ZMod m)ˣ`, which is the totient.
    have hcard :
        Fintype.card (Units (ZMod m)) = Nat.totient m :=
      ZMod.card_units_eq_totient (n := m)
    -- Step 2.6.2: Combine `orderOf_dvd_card` with the cardinality computation.
    simpa [hcard] using (orderOf_dvd_card (x := u))
  have hdiv : n ∣ Nat.totient m := by
    -- Step 2.6.3: Substitute the value of `orderOf u`.
    simpa [horder_eq] using horder_dvd
  -- Step 2.7: Replace `m` by `a ^ n - 1` to conclude.
  simpa [m, hmdef] using hdiv
