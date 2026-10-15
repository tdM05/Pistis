import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

/-- Auxiliary arithmetic fact used in the main proof. -/
lemma nat_pos_pos_sum_three {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 3) : a = 1 ∨ b = 1 := by
  -- Step 1: bound `a` from above using `a ≤ a + b = 3`.
  have ha_le_three : a ≤ 3 := by
    -- Step 1.1: `a ≤ a + b` and `a + b = 3`.
    have := Nat.le_add_right a b
    simpa [h] using this
  -- Step 2: perform a complete case split on the possible values of `a`.
  cases' a with a₀
  · -- Step 2.1: `a = 0` contradicts `ha : 0 < a`.
    have : False := by simp at ha
    exact this.elim
  · cases' a₀ with a₁
    · -- Step 2.2: `a = 1`.
      exact Or.inl rfl
    · cases' a₁ with a₂
      · -- Step 2.3: `a = 2`, hence `b = 1`.
        have hb_eq : b = 1 := by
          have : 2 + b = 2 + 1 := by simpa using h
          exact Nat.add_left_cancel this
        exact Or.inr hb_eq
      · cases' a₂ with a₃
        · -- Step 2.4: `a = 3` forces `b = 0`.
          have hb_zero : b = 0 := by
            have : 3 + b = 3 := by simpa using h
            have : 3 + b = 3 + 0 := by simpa using this
            exact Nat.add_left_cancel this
          have : False := by simp [hb_zero] at hb
          exact this.elim
        · -- Step 2.5: `a ≥ 4` contradicts `a ≤ 3`.
          have hfour_le :
              4 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ a₃))) := by
            have := Nat.zero_le a₃
            exact Nat.succ_le_succ
              (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ this)))
          exact absurd (le_trans hfour_le ha_le_three) (by omega)



/-Informal Statement

Prove that $x^3 - 9$ is irreducible in $\mathbb{F}_{31}$.
-/

/-Informal Proof

If $p(x) = x^3-9$ were reducible, it would have a linear factor, since it either has a linear factor and a quadratic factor or three linear factors. We can then verify by brute force that $p(x)\neq 0$ for $x \in \mathbb{F}_31$.
-/

theorem Artin_exercise_11_4_6c : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  -- Step 1: switch to a named polynomial `p` to ease rewriting goals.
  classical
  -- Step 1.1: register that 31 is prime so `ℤ/31ℤ` is a field.
  haveI : Fact (Nat.Prime 31) := ⟨by decide⟩
  haveI : NeZero (31 : ℕ) := ⟨by decide⟩
  set p : Polynomial (ZMod 31) := X^3 - Polynomial.C (9 : ZMod 31) with hp_def
  have : Irreducible p := by
    -- Step 2: record that `p` is monic.
    have hp_monic : p.Monic := by
      simpa [p, hp_def] using
        (Polynomial.monic_X_pow_sub_C (R := ZMod 31) (n := 3) (a := (9 : ZMod 31)))
    -- Step 3: fix the fact that `p` has degree three.
    have hp_nat : p.natDegree = 3 := by
      simp [p,
        (Polynomial.natDegree_X_pow_sub_C (R := ZMod 31) (n := 3) (r := (9 : ZMod 31)))]
    -- Step 4: show that `p` has no roots in `𝔽₃₁` using brute-force decision.
    have hp_no_root : ∀ a : ZMod 31, p.eval a ≠ 0 := by
      -- Step 4.0: compute `9^10` modulo `31`.
      have hdiv : (31 : ℕ) ∣ 9 ^ 10 - 5 := by decide
      have hle : (5 : ℕ) ≤ 9 ^ 10 := by decide
      have hpow_val :
          (9 : ZMod 31) ^ 10 = (5 : ZMod 31) := by
        have hcast := (Nat.cast_pow (α := ZMod 31) 9 10).symm
        have hdiff :
            ((9 ^ 10 : ℕ) : ZMod 31) - (5 : ZMod 31) = 0 := by
          have : ((9 ^ 10 - 5 : ℕ) : ZMod 31) = 0 :=
            (ZMod.natCast_eq_zero_iff _ _).2 hdiv
          simpa [Nat.cast_sub hle] using this
        have : ((9 ^ 10 : ℕ) : ZMod 31) = (5 : ZMod 31) :=
          sub_eq_zero.mp hdiff
        exact hcast.trans this
      have hpow_ne : (9 : ZMod 31) ^ 10 ≠ 1 := by
        have h5 : (5 : ZMod 31) ≠ (1 : ZMod 31) := by
          intro h
          have hv := congrArg ZMod.val h
          have h5val :
              (5 : ZMod 31).val = 5 :=
            ZMod.val_natCast_of_lt (show 5 < 31 by decide)
          have h1val :
              (1 : ZMod 31).val = 1 :=
            ZMod.val_natCast_of_lt (show 1 < 31 by decide)
          have hval : (5 : ℕ) = 1 := by
            simp [h5val, h1val] at hv
          exact (by decide : (5 : ℕ) ≠ 1) hval
        simpa [hpow_val] using h5
      intro a
      -- Step 4.1: show `a^3 = 9` leads to a contradiction via Fermat.
      have ha_cube_ne : a ^ 3 ≠ (9 : ZMod 31) := by
        intro hcube
        have ha_ne_zero : a ≠ 0 := by
          intro hz
          have hzero : (0 : ZMod 31) = (9 : ZMod 31) := by simpa [hz] using hcube
          have h9ne : (9 : ZMod 31) ≠ 0 := by
            intro hzero'
            have hdiv' : 31 ∣ 9 :=
              (ZMod.natCast_eq_zero_iff 9 31).1 hzero'
            rcases hdiv' with ⟨k, hk⟩
            have hk_ne_zero : k ≠ 0 := by
              intro hk0
              have : (9 : ℕ) = 0 := by simp [hk0] at hk
              exact (by decide : (9 : ℕ) ≠ 0) this
            have hk_pos : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk_ne_zero)
            have hle' : 31 ≤ 9 := by
              have := Nat.mul_le_mul_left 31 hk_pos
              simpa [hk, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
            exact (by decide : ¬31 ≤ 9) hle'
          exact h9ne (by simpa using hzero.symm)
        have hfermat : a ^ 30 = 1 := by
          simpa using (ZMod.pow_card_sub_one_eq_one (p := 31) (a := a) ha_ne_zero)
        have hpow_eq : (9 : ZMod 31) ^ 10 = 1 := by
          calc
            (9 : ZMod 31) ^ 10 = (a ^ 3) ^ 10 := by simp [hcube]
            _ = a ^ (3 * 10) := by
              simpa [Nat.mul_comm] using (pow_mul a 3 10).symm
            _ = a ^ 30 := by
              have hmul : 3 * 10 = 30 := by decide
              simp [hmul]
            _ = 1 := hfermat
        exact hpow_ne hpow_eq
      -- Step 4.2: translate `a^3 ≠ 9` into `p.eval a ≠ 0`.
      simpa [p, hp_def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C] using sub_ne_zero.mpr ha_cube_ne
    -- Step 5: reduce irreducibility to the monic criterion about factorisations.
    refine (Polynomial.Monic.irreducible_iff_natDegree hp_monic).2 ?_
    -- Step 5.1: show `p ≠ 1` using the degree computation.
    refine ⟨?_, ?_⟩
    · -- Step 5.1.1: `natDegree 1 = 0`, contradicting `hp_nat = 3`.
      intro hp_one
      have := congrArg Polynomial.natDegree hp_one
      simp [hp_nat] at this
    -- Step 5.2: analyse all monic factorizations `p = f * g`.
    · intro f g hf hg hfg
      -- Step 5.2.1: note that monic polynomials are nonzero, hence degrees add.
      have hf_ne_zero : f ≠ 0 := hf.ne_zero
      have hg_ne_zero : g ≠ 0 := hg.ne_zero
      have hdeg_mul :
          (f * g).natDegree = f.natDegree + g.natDegree :=
        Polynomial.natDegree_mul hf_ne_zero hg_ne_zero
      have hsum : f.natDegree + g.natDegree = 3 := by
        simpa [hfg, hp_nat] using hdeg_mul.symm
      -- Step 5.2.2: helper showing that linear monic factors would give a root.
      have aux_linear :
          ∀ {q r : Polynomial (ZMod 31)},
            q.Monic → r.Monic → q * r = p → q.natDegree = 1 → False := by
        intro q r hq hr hqr hdeg
        -- Step 5.2.2.1: express `q` explicitly as `X + C (q.coeff 0)`.
        have hq_shape : q = X + C (q.coeff 0) := hq.eq_X_add_C hdeg
        set c := q.coeff 0
        have hq_shape' : q = X + C c := by simpa [c] using hq_shape
        -- Step 5.2.2.2: evaluate at `-q.coeff 0` to obtain a root of `q`.
        have hq_root' : q.eval (-c) = 0 := by
          have : (X + C c).eval (-c) = 0 := by simp
          simp [hq_shape']
        have hq_root : q.eval (-q.coeff 0) = 0 := by simpa [c] using hq_root'
        -- Step 5.2.2.3: transfer the root to `p` via the factorisation.
        have hp_zero : p.eval (-q.coeff 0) = 0 := by
          have : (q * r).eval (-q.coeff 0) = 0 := by
            simp [Polynomial.eval_mul, hq_root]
          simpa [hqr] using this
        -- Step 5.2.2.4: contradict Step 4 (no roots).
        exact (hp_no_root (-q.coeff 0)) hp_zero
      -- Step 5.2.3: linear factors are forbidden on either side.
      have hf_ne_one : f.natDegree ≠ 1 := by
        intro hf_deg
        exact aux_linear hf hg hfg hf_deg
      have hg_ne_one : g.natDegree ≠ 1 := by
        intro hg_deg
        have : g * f = p := by simpa [mul_comm] using hfg
        exact aux_linear hg hf this hg_deg
      -- Step 5.2.4: deduce that one factor must have degree zero.
      by_contra hzero
      -- Step 5.2.4.1: extract that both degrees are positive from the negation.
      have hf_nz : f.natDegree ≠ 0 := by
        intro hf_deg
        exact hzero (Or.inl hf_deg)
      have hg_nz : g.natDegree ≠ 0 := by
        intro hg_deg
        exact hzero (Or.inr hg_deg)
      have hf_pos : 0 < f.natDegree := Nat.pos_of_ne_zero hf_nz
      have hg_pos : 0 < g.natDegree := Nat.pos_of_ne_zero hg_nz
      -- Step 5.2.4.2: positive degrees summing to `3` force one of them to be `1`.
      have : f.natDegree = 1 ∨ g.natDegree = 1 :=
        nat_pos_pos_sum_three hf_pos hg_pos hsum
      -- Step 5.2.4.3: contradict the previous “no linear factor” statements.
      cases this with
      | inl hf_deg => exact hf_ne_one hf_deg
      | inr hg_deg => exact hg_ne_one hg_deg
  -- Step 6: return to the original goal using `hp_def`.
  simpa [p, hp_def] using this
