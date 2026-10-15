import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $H$ be a subgroup of the additive group of rational numbers with the property that $1 / x \in H$ for every nonzero element $x$ of $H$. Prove that $H=0$ or $\mathbb{Q}$.
-/

/-Informal Proof

Solution: First, suppose there does not exist a nonzero element in $H$. Then $H=0$.
Now suppose there does exist a nonzero element $a \in H$; without loss of generality, say $a=p / q$ in lowest terms for some integers $p$ and $q$ - that is, $\operatorname{gcd}(p, q)=1$. Now $q \cdot \frac{p}{q}=p \in H$, and since $q / p \in H$, we have $p \cdot \frac{q}{p} \in H$. There exist integers $x, y$ such that $q x+p y=1$; note that $q x \in H$ and $p y \in H$, so that $1 \in H$. Thus $n \in H$ for all $n \in \mathbb{Z}$. Moreover, if $n \neq 0,1 / n \in H$. Then $m / n \in H$ for all integers $m, n$ with $n \neq 0$; hence $H=\mathbb{Q}$.
-/

theorem Dummit_Foote_exercise_2_1_13 (H : AddSubgroup ℚ) {x : ℚ}
  (hH : (x ∈ H ∧ x ≠ 0) → (1 / x) ∈ H):
  H = ⊥ ∨ H = ⊤ := by
  sorry

/-
Counterexample summary:
Step 0.1: Consider the additive subgroup `H = AddSubgroup.zmultiples (1 : ℚ)`, i.e. the integers inside ℚ.
Step 0.2: Pick the specific element `x = 0`. Then the hypothesis `(x ∈ H ∧ x ≠ 0)` is false, so the reciprocal condition holds vacuously.
Step 0.3: The subgroup `H` is neither `{0}` (because `1 ∈ H`) nor `ℚ` (because `(1 / 2) ∉ H`), so the original statement fails.
-/

theorem Dummit_Foote_exercise_2_1_13_neg :
    ∃ H : AddSubgroup ℚ, ∃ x : ℚ,
      ((x ∈ H ∧ x ≠ 0) → (1 / x) ∈ H) ∧ ¬ (H = ⊥ ∨ H = ⊤) := by
  classical
  -- Step 1: Choose the integer subgroup and the element x = 0.
  refine ⟨AddSubgroup.zmultiples (1 : ℚ), 0, ?_, ?_⟩
  -- Step 2: The reciprocal hypothesis is vacuous because 0 ≠ 0 is false.
  · -- Step 2.1: Assume the (impossible) premise and derive a contradiction.
    intro hx
    -- Step 2.2: Contradict `0 ≠ 0`, so any conclusion (in particular membership) follows.
    exact (hx.2 rfl).elim
  -- Step 3: Show that the subgroup is neither ⊥ nor ⊤.
  · -- Step 3.1: Handle the two disjuncts separately.
    intro h
    -- Step 3.2: First eliminate the possibility `H = ⊥`.
    cases h with
    | inl hbot =>
        -- Step 3.2.1: Note that 1 lies in the subgroup of integer multiples.
        have h_one :
            (1 : ℚ) ∈ AddSubgroup.zmultiples (1 : ℚ) := by
          -- Step 3.2.1.1: Witness membership via the integer 1.
          refine ⟨1, by simp⟩
        -- Step 3.2.2: But 1 ∉ ⊥, so we get a contradiction.
        have : (1 : ℚ) ∈ (⊥ : AddSubgroup ℚ) := by simp [hbot] at h_one
        simp at this
    | inr htop =>
        -- Step 3.3: Show `(1 / 2)` is absent, so equality with ⊤ is impossible.
        have h_half_mem :
            (1 / 2 : ℚ) ∈ AddSubgroup.zmultiples (1 : ℚ) := by
          -- Step 3.3.1: Transport the membership from ⊤ via `htop`.
          simp [htop]
        -- Step 3.3.2: Decode membership in the zmultiples to reach a contradiction.
        obtain ⟨k, hk⟩ := h_half_mem
        -- Step 3.3.3: Reduce the statement to an impossible equation in integers.
        have hk_rat : (k : ℚ) = (1 / 2 : ℚ) := by
          simpa [zsmul_eq_mul] using hk
        -- Step 3.3.4: Multiply the equality by 2 and interpret it back in ℤ.
        have hk_two :
            ((2 : ℚ) * (k : ℚ)) = (1 : ℚ) := by
          -- Step 3.3.4.1: Multiply the forbidden equality by 2 and simplify.
          have h := congrArg (fun t : ℚ => (2 : ℚ) * t) hk_rat
          have h_one : (2 : ℚ) * (1 / 2 : ℚ) = (1 : ℚ) := by norm_num
          exact h.trans h_one
        have hk_int : (2 * k : ℤ) = 1 := by
          exact_mod_cast hk_two
        -- Step 3.3.5: The left-hand side is even, contradicting `Int.not_even_one`.
        have h_even : Even (1 : ℤ) := by
          have h_even_mul : Even (2 * k : ℤ) := ⟨k, by simp [two_mul]⟩
          rcases h_even_mul with ⟨m, hm⟩
          refine ⟨m, ?_⟩
          exact ((Eq.symm hm).trans hk_int).symm
        exact Int.not_even_one h_even

/-
Corrected statement summary:
Step 0.1: Assume that *every* nonzero element of `H` has its reciprocal inside `H`.
Step 0.2: Either `H` is trivial, or we select a nonzero element `x ∈ H`.
Step 0.3: Use the numerator/denominator description of `x` together with the reciprocal condition to show both numbers belong to `H`.
Step 0.4: Bézout’s identity yields a linear combination equalling `1`, so all integers lie in `H`.
Step 0.5: The reciprocal condition then places all rational numbers in `H`, forcing `H = ℚ`.
-/

theorem Dummit_Foote_exercise_2_1_13_corrected (H : AddSubgroup ℚ)
    (hH : ∀ ⦃x : ℚ⦄, x ∈ H → x ≠ 0 → (1 / x) ∈ H) :
    H = ⊥ ∨ H = ⊤ := by
  classical
  -- Step 1: Split on the possibility that `H` is the trivial subgroup.
  by_cases hbot : H = ⊥
  · -- Step 1.1: If `H = ⊥`, the desired disjunction holds immediately.
    exact Or.inl hbot
  -- Step 2: Extract a nonzero element of `H` from the assumption `H ≠ ⊥`.
  obtain ⟨x, hxH, hx0⟩ :
      ∃ x : ℚ, x ∈ H ∧ x ≠ 0 := by
    -- Step 2.1: Argue by contradiction that every element would be zero.
    classical
    by_contra hx
    -- Step 2.2: Show `H ≤ ⊥` if the negated existential held.
    have h_le : H ≤ (⊥ : AddSubgroup ℚ) := by
      intro y hy
      have hy0 : y = 0 := by
        -- Step 2.2.1: If `y ≠ 0`, we contradict `hx`.
        by_contra hy0
        exact hx ⟨y, hy, hy0⟩
      simp [hy0]
    -- Step 2.3: Conclude `H = ⊥`, contradicting the initial assumption.
    exact hbot (le_antisymm h_le bot_le)
  -- Step 3: Record the standard numerator/denominator relations for `x`.
  set p : ℤ := x.num
  set q : ℕ := x.den
  have h_num_relation :
      (q : ℚ) * x = (p : ℚ) := by
    -- Step 3.1: Clear denominators from `Rat.num_div_den`.
    have hnum := congrArg (fun t : ℚ => (q : ℚ) * t) (Rat.num_div_den x)
    have hq_ne_zero : (q : ℚ) ≠ 0 := by
      exact_mod_cast (Rat.den_ne_zero x)
    simp [p, q, mul_comm]
  have h_den_relation :
      (p : ℚ) * x⁻¹ = (q : ℚ) := by
    -- Step 3.2: Multiply the previous relation by `x⁻¹` on the right.
    calc
      (p : ℚ) * x⁻¹
          = ((q : ℚ) * x) * x⁻¹ := by simp [h_num_relation]
      _ = (q : ℚ) * (x * x⁻¹) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
      _ = (q : ℚ) := by
            simp [hx0]
  -- Step 4: Deduce that both the numerator and denominator belong to `H`.
  have hp_mem : (p : ℚ) ∈ H := by
    -- Step 4.1: `p` is a ℤ-multiple of `x`.
    have hzsmul := H.zsmul_mem hxH (q : ℤ)
    -- Step 4.2: Rewrite the scalar multiple explicitly.
    simpa [p, q, zsmul_eq_mul, h_num_relation] using hzsmul
  have h_inv_mem : x⁻¹ ∈ H := by
    -- Step 4.2.5: Restate the reciprocal condition using `x⁻¹`.
    simpa [one_div] using hH hxH hx0
  have hq_mem : (q : ℚ) ∈ H := by
    -- Step 4.3: `q` is a ℤ-multiple of `1 / x`.
    have hzsmul := H.zsmul_mem h_inv_mem p
    have hzsmul_eq :
        ((p : ℤ) • x⁻¹) = (q : ℚ) := by
      simp [p, zsmul_eq_mul, h_den_relation]
    simpa [hzsmul_eq] using hzsmul
  -- Step 5: Invoke Bézout to express `1` as an integer linear combination of `p` and `q`.
  have h_coprime : Nat.Coprime x.num.natAbs x.den := x.reduced
  have h_gcd :
      Int.gcd p (q : ℤ) = 1 := by
    -- Step 5.1: Translate the coprimality statement to the integer gcd.
    have h_nat : Nat.gcd x.num.natAbs x.den = 1 := h_coprime.gcd_eq_one
    simpa [p, q, Int.gcd_def, Int.natAbs_natCast] using h_nat
  have h_bezout :
      (p : ℚ) * (Int.gcdA p (q : ℤ) : ℚ) +
          (q : ℚ) * (Int.gcdB p (q : ℤ) : ℚ) = (1 : ℚ) := by
    -- Step 5.2: Cast Bézout’s identity from ℤ to ℚ.
    have h_int :
        (1 : ℤ) =
            p * Int.gcdA p (q : ℤ) + (q : ℤ) * Int.gcdB p (q : ℤ) := by
      simpa [h_gcd] using Int.gcd_eq_gcd_ab p (q : ℤ)
    exact_mod_cast h_int.symm
  -- Step 6: Show `1 ∈ H` using closure under integer combinations.
  let a : ℤ := Int.gcdA p (q : ℤ)
  let b : ℤ := Int.gcdB p (q : ℤ)
  have h_one_mem : (1 : ℚ) ∈ H := by
    -- Step 6.1: Each term in the Bézout combination lies in `H`.
    have ha_mem : (a : ℤ) • (p : ℚ) ∈ H := H.zsmul_mem hp_mem a
    have hb_mem : (b : ℤ) • (q : ℚ) ∈ H := H.zsmul_mem hq_mem b
    -- Step 6.2: Combine the two elements and rewrite their sum as 1.
    have h_sum :
        (↑a * (p : ℚ) + ↑b * (q : ℚ)) ∈ H := by
      simpa [a, b, zsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc,
        add_comm, add_left_comm, add_assoc] using
        H.add_mem ha_mem hb_mem
    -- Step 6.3: Use the Bézout equality to identify the sum with 1.
    have h_sum_eq :
        (↑a * (p : ℚ)) + (↑b * (q : ℚ)) = (1 : ℚ) := by
      simpa [a, b, mul_comm, mul_left_comm, mul_assoc, add_comm,
        add_left_comm, add_assoc] using h_bezout
    simpa [h_sum_eq] using h_sum
  -- Step 7: Deduce that all integers (and their reciprocals) lie in `H`.
  have h_int_mem : ∀ m : ℤ, (m : ℚ) ∈ H := by
    -- Step 7.1: Multiply `1` by arbitrary integers inside the subgroup.
    intro m
    have hmul : (m : ℤ) • (1 : ℚ) ∈ H := H.zsmul_mem h_one_mem m
    simpa [zsmul_eq_mul] using hmul
  have h_int_inv_mem :
      ∀ m : ℤ, m ≠ 0 → (1 / (m : ℚ)) ∈ H := by
    intro m hm
    -- Step 7.2: Apply the reciprocal hypothesis to each nonzero integer.
    have hm_mem : (m : ℚ) ∈ H := h_int_mem m
    have hm_ne_zero : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    exact hH hm_mem hm_ne_zero
  -- Step 8: Show that every rational number belongs to `H`.
  have h_all_rat : ∀ r : ℚ, r ∈ H := by
    intro r
    -- Step 8.1: `1 / r.den` belongs to `H` because `r.den` is a positive integer.
    have h_inv_den :
        (1 / (r.den : ℚ)) ∈ H :=
      h_int_inv_mem (r.den : ℤ)
        (by exact_mod_cast (Rat.den_ne_zero r))
    -- Step 8.2: Multiply the inverse denominator by the numerator.
    have hzsmul := H.zsmul_mem h_inv_den r.num
    -- Step 8.3: Recognize the resulting element as `r` itself.
    have hzsmul_eq :
        ((r.num : ℤ) • (r.den : ℚ)⁻¹) = r := by
      have h_ratio :
          (r.num : ℚ) * (r.den : ℚ)⁻¹ = r := by
        simpa [div_eq_mul_inv] using (Rat.num_div_den r)
      simpa [zsmul_eq_mul, one_div] using h_ratio
    -- Step 8.4: Convert the membership statement using the same normalization.
    simpa [one_div, hzsmul_eq] using hzsmul
  -- Step 9: Conclude that `H = ⊤` by extensionality.
  have h_top_le : (⊤ : AddSubgroup ℚ) ≤ H := by
    intro q _
    exact h_all_rat q
  exact Or.inr (le_antisymm le_top h_top_le)
