import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $N$ be a positive integer. Let $M$ be an integer relatively prime to $N$ and let $d$ be an integer relatively prime to $\varphi(N)$, where $\varphi$ denotes Euler's $\varphi$-function. Prove that if $M_{1} \equiv M^{d} \pmod N$ then $M \equiv M_{1}^{d^{\prime}} \pmod N$ where $d^{\prime}$ is the inverse of $d \bmod \varphi(N)$: $d d^{\prime} \equiv 1 \pmod {\varphi(N)}$.
-/

/-Informal Proof

Note that there is some $k \in \mathbb{Z}$ such that $M^{d d^{\prime}} \equiv M^{k \varphi(N)+1} \equiv\left(M^{\varphi(N)}\right)^k \cdot M \bmod N$. By Euler's Theorem we have $M^{\varphi(N)} \equiv 1 \bmod N$, so that $M_1^{d^{\prime}} \equiv M \bmod N$.
-/

theorem Dummit_Foote_exercise_8_1_12 {N : ℕ} (hN : N > 0) {M M': ℤ} {d : ℕ}
  (hMN : M.gcd N = 1) (hMd : d.gcd N.totient = 1)
  (hM' : M' ≡ M^d [ZMOD N]) :
  ∃ d' : ℕ, d' * d ≡ 1 [ZMOD N.totient] ∧
  M ≡ M'^d' [ZMOD N] := by
  classical
  -- Step 1: Introduce the abbreviation φ := N.totient and record its positivity.
  set φ := N.totient with hφDef
  have hφpos : 0 < φ := by
    -- Step 1.1: Apply the known positivity criterion for Euler's totient.
    simpa [φ, hφDef] using (Nat.totient_pos).2 hN
  -- Step 1.2: Register `φ ≠ 0` so that we may work inside `ZMod φ`.
  haveI : NeZero φ := ⟨ne_of_gt hφpos⟩
  -- Step 2: Use the gcd hypothesis on `d` to view `d` as a unit modulo φ.
  have hCoprime : Nat.Coprime d φ := by
    -- Step 2.1: Rewrite the gcd statement as a coprimality statement.
    simpa [φ, hφDef, Nat.coprime_iff_gcd_eq_one] using hMd
  -- Step 2.2: Package the modular inverse of `d` inside (ZMod φ)ˣ.
  let dUnit : (ZMod φ)ˣ := ZMod.unitOfCoprime d hCoprime
  -- Step 2.3: Define d' as the natural representative of the inverse of d modulo φ.
  let d' : ℕ := ((dUnit⁻¹ : (ZMod φ)ˣ) : ZMod φ).val
  -- Step 2.4: Identify the coercion of d' back into ZMod φ.
  have hd'cast :
      (d' : ZMod φ) = ((dUnit⁻¹ : (ZMod φ)ˣ) : ZMod φ) := by
    -- Step 2.4.1: Use the canonical property of `val` in `ZMod`.
    dsimp [d']
    simp
  -- Step 2.5: Show that d' really is the multiplicative inverse of d in ZMod φ.
  have hdMulZ :
      (d' : ZMod φ) * (d : ZMod φ) = (1 : ZMod φ) := by
    -- Step 2.5.1: Start from the unit equation u⁻¹ * u = 1 in (ZMod φ)ˣ.
    have hdUnits :
        ((dUnit⁻¹ : (ZMod φ)ˣ) * dUnit : (ZMod φ)ˣ) = 1 := by
      -- Step 2.5.1.1: Directly apply the unit identity.
      simp
    -- Step 2.5.2: Push the equation down to ZMod φ and simplify.
    have hdZmod :
        ((dUnit⁻¹ : (ZMod φ)ˣ) : ZMod φ) *
            ((dUnit : (ZMod φ)ˣ) : ZMod φ) = 1 := by
      -- Step 2.5.2.1: Apply the coercion map from units to the ring.
      simp
    -- Step 2.5.3: Recognise that the second factor is just the original natural number d.
    simp [hd'cast, dUnit, ZMod.coe_unitOfCoprime]
  -- Step 2.6: Convert the equality in ZMod into a natural-number congruence.
  have hdMulNat :
      ((d' * d : ℕ) : ZMod φ) = (1 : ZMod φ) := by
    -- Step 2.6.1: Leverage ring-theoretic compatibility of natural-number multiplication.
    simpa [Nat.cast_mul] using hdMulZ
  have hdModNat : d' * d ≡ 1 [MOD φ] := by
    -- Step 2.6.2: Translate the equality of representatives into a modular congruence.
    have hEq :
        ((d' * d : ℕ) : ZMod φ) = ((1 : ℕ) : ZMod φ) := by
      -- Step 2.6.2.a: Align the equality with the lemma’s expected format.
      simpa using hdMulNat
    simpa using
      (ZMod.natCast_eq_natCast_iff (d' * d) 1 φ).1 hEq
  -- Step 3: Prepare the congruence modulo N by moving into ZMod N.
  have hNne : N ≠ 0 := ne_of_gt hN
  -- Step 3.1: Register the non-trivial modulus for ZMod N.
  haveI : NeZero N := ⟨hNne⟩
  -- Step 3.2: Rewrite the given congruence `hM'` as an equality inside ZMod N.
  have hM'_zmod :
      (M' : ZMod N) = (M : ZMod N) ^ d := by
    -- Step 3.2.1: Use the ZMod characterization of integer congruence.
    simpa using
      (ZMod.intCast_eq_intCast_iff M' (M ^ d) N).2 hM'
  -- Step 4: Prove that `M` is a unit modulo `N` via Bézout.
  have hBezout :
      (1 : ℤ) =
        M * Int.gcdA M (N : ℤ) +
          (N : ℤ) * Int.gcdB M (N : ℤ) := by
    -- Step 4.1: Start from the standard Bézout identity over the integers.
    have := Int.gcd_eq_gcd_ab M (N : ℤ)
    -- Step 4.2: Substitute the gcd value supplied by hypothesis.
    simpa [hMN] using this
  -- Step 4.3: Reduce Bézout's identity modulo N to obtain an explicit inverse.
  have hUnitMul :
      (M : ZMod N) * (Int.gcdA M (N : ℤ) : ZMod N) = 1 := by
    -- Step 4.3.1: Transfer the integer identity into ZMod N.
    have h :=
      congrArg (fun x : ℤ => (x : ZMod N)) hBezout
    -- Step 4.3.2: Simplify the computation using the fact that N ≡ 0 in ZMod N.
    simpa using h.symm
  -- Step 4.4: Use the exhibited inverse to upgrade M to a unit in ZMod N.
  have hUnitM : IsUnit (M : ZMod N) := by
    -- Step 4.4.1: Construct the unit explicitly with the inverse supplied by Bézout.
    refine ⟨⟨(M : ZMod N), (Int.gcdA M (N : ℤ) : ZMod N), ?_, ?_⟩, rfl⟩
    · -- Step 4.4.1.1: Verify `val * inv = 1`.
      simpa using hUnitMul
    · -- Step 4.4.1.2: Verify `inv * val = 1` (commutativity makes the verification immediate).
      simpa [mul_comm] using hUnitMul
  -- Step 4.5: Choose a concrete unit representative and remember its value.
  obtain ⟨uM, huM⟩ := hUnitM
  -- Step 5: Translate hM'_zmod so that it uses the chosen unit representative.
  have hM'_zmod' :
      (M' : ZMod N) = (↑uM : ZMod N) ^ d := by
    -- Step 5.1: Substitute the stored identity `huM`.
    simpa [huM] using hM'_zmod
  -- Step 5.2: Record Euler's theorem for the unit `uM`.
  have hPowTotUnit : uM ^ φ = 1 := ZMod.pow_totient uM
  -- Step 5.3: Translate Euler's theorem back to ZMod N.
  have hPowTotVal :
      (↑uM : ZMod N) ^ φ = (1 : ZMod N) := by
    -- Step 5.3.1: Coerce the unit equation to the base ring.
    simpa using congrArg
      (fun x : (ZMod N)ˣ => (x : ZMod N)) hPowTotUnit
  -- Step 6: Raise the congruence for M' to the power d' in ZMod N.
  have hPow :
      (M' : ZMod N) ^ d' = (↑uM : ZMod N) ^ (d * d') := by
    -- Step 6.1: Raise the equality `hM'_zmod'` to the exponent d'.
    have := congrArg (fun x : ZMod N => x ^ d') hM'_zmod'
    -- Step 6.2: Simplify using the law `(x^m)^n = x^(m*n)`.
    simpa [pow_mul, Nat.mul_comm] using this
  -- Step 7: Compare the exponent `d * d'` with the exponent predicted by Euler's theorem.
  have hTarget :
      (↑uM : ZMod N) ^ (d * d') = (↑uM : ZMod N) := by
    -- Step 7.1: Split into the two cases φ = 1 and φ ≠ 1.
    by_cases hφ1 : φ = 1
    · -- Step 7.1.a: When φ = 1, Euler's theorem forces the unit to be 1.
      -- Step 7.1.a.1: `uM ^ 1 = 1`, hence `uM = 1`.
      have huM_one : uM = 1 := by
        simpa [φ, hφ1] using hPowTotUnit
      -- Step 7.1.a.2: Reduce the equality in ZMod N.
      have : (↑uM : ZMod N) = 1 := by simp [huM_one]
      -- Step 7.1.a.3: All powers of 1 are 1, giving the desired equality.
      simp [this]
    · -- Step 7.1.b: When φ ≠ 1, the difference `d * d' - 1` is a non-negative multiple of φ.
      -- Step 7.1.b.1: Both d and d' are positive in this case.
      have hd_ne : d ≠ 0 := by
        intro hdZero
        have : φ = 1 := by
          -- Step 7.1.b.1.i: If d = 0, then gcd(d, φ) = φ = 1.
          simpa [φ, hφDef, hdZero] using hMd
        exact hφ1 this
      have hd'_ne : d' ≠ 0 := by
        intro hd'Zero
        -- Step 7.1.b.1.ii: If d' = 0, the congruence gives φ = 1.
        have hZero : 0 ≡ 1 [MOD φ] := by
          -- Step 7.1.b.1.ii.a: Convert the congruence to a divisibility statement.
          simpa [hd'Zero, Nat.zero_mul] using hdModNat
        have hDivInt : (φ : ℤ) ∣ (1 : ℤ) := (Nat.modEq_iff_dvd).1 hZero
        have hDivNat : φ ∣ 1 := by
          -- Step 7.1.b.1.ii.b: Translate divisibility from ℤ back to ℕ.
          simpa using (Int.ofNat_dvd_natCast).1 hDivInt
        have : φ = 1 := Nat.dvd_one.mp hDivNat
        exact hφ1 this
      -- Step 7.1.b.2: Record strict positivity of the product d * d'.
      have hdProdPos : 0 < d * d' :=
        Nat.mul_pos (Nat.pos_of_ne_zero hd_ne) (Nat.pos_of_ne_zero hd'_ne)
      -- Step 7.1.b.3: Turn the congruence `d' * d ≡ 1` into an equality `d * d' = 1 + φ * k`.
      have hDivNat :
          φ ∣ d * d' - 1 := by
        -- Step 7.1.b.3.i: Use the superior order version with the inequality hypothesis.
        have hOnele : 1 ≤ d * d' := Nat.succ_le_of_lt hdProdPos
        have hSymm : 1 ≡ d * d' [MOD φ] := by
          -- Step 7.1.b.3.ii: Symmetry of congruence allows us to reverse the operands.
          simpa [Nat.mul_comm] using hdModNat.symm
        -- Step 7.1.b.3.iii: Apply the characterization of congruence via divisibility.
        exact (Nat.modEq_iff_dvd' hOnele).1 hSymm
      -- Step 7.1.b.4: Choose the auxiliary multiplier k witnessing the divisibility.
      obtain ⟨k, hk⟩ := hDivNat
      -- Step 7.1.b.5: Rewrite the exponent `d * d'` using the obtained equality.
      have hk' : d * d' = 1 + φ * k := by
        -- Step 7.1.b.5.i: Reassemble the product after moving the term across the equality.
        have hOnele : 1 ≤ d * d' := Nat.succ_le_of_lt hdProdPos
        have h1 :
            d * d' = (d * d' - 1) + 1 :=
          (Nat.sub_add_cancel hOnele).symm
        have h2 :
            (d * d' - 1) + 1 = φ * k + 1 :=
          congrArg (fun t => t + 1) hk
        have h3 : d * d' = φ * k + 1 := h1.trans h2
        simpa [Nat.add_comm] using h3
      -- Step 7.1.b.6: Expand the power using the decomposition from hk'.
      have hPowRewrite :
          (↑uM : ZMod N) ^ (d * d') =
            (↑uM : ZMod N) ^ (φ * k) * (↑uM : ZMod N) := by
        -- Step 7.1.b.6.i: Replace the exponent via hk'.
        have h1 :
            (↑uM : ZMod N) ^ (d * d') =
              (↑uM : ZMod N) ^ (φ * k + 1) := by
          simp [hk', Nat.add_comm]
        -- Step 7.1.b.6.ii: Apply the power-addition rule.
        have h2 :
            (↑uM : ZMod N) ^ (φ * k + 1) =
              (↑uM : ZMod N) ^ (φ * k) * (↑uM : ZMod N) := by
          simp [pow_add, pow_one]
        exact h1.trans h2
      -- Step 7.1.b.7: Evaluate the factor involving φ using Euler's theorem.
      have hPowPhi :
          (↑uM : ZMod N) ^ (φ * k) = (1 : ZMod N) := by
        calc
          (↑uM : ZMod N) ^ (φ * k)
              = ((↑uM : ZMod N) ^ φ) ^ k := by
                rw [pow_mul]
          _ = (1 : ZMod N) ^ k := by
                simp [hPowTotVal]
          _ = 1 := by simp
      -- Step 7.1.b.8: Combine the evaluations to obtain the desired equality.
      have hPowRewrite' :
          (↑uM : ZMod N) ^ (d * d') =
            (↑uM : ZMod N) := by
        simpa [hPowPhi] using hPowRewrite
      simpa using hPowRewrite'
  -- Step 7.2: Combine the two power computations.
  have hPowFinal :
      (M' : ZMod N) ^ d' = (↑uM : ZMod N) := by
    -- Step 7.2.1: Apply the equality linking both exponents.
    exact hPow.trans hTarget
  -- Step 7.3: Substitute back the value of ↑uM in terms of M.
  have hPowFinal' :
      (M' : ZMod N) ^ d' = (M : ZMod N) := by
    -- Step 7.3.1: Replace the unit representative with the original element.
    simpa [huM] using hPowFinal
  -- Step 8: Convert the ZMod equality into the desired congruence over the integers.
  have hFinal :
      M'^d' ≡ M [ZMOD N] := by
    -- Step 8.1: Express the equality using integer representatives.
    have hEq :
        ((M'^d' : ℤ) : ZMod N) = (M : ZMod N) := by
      -- Step 8.1.1: Map the power into ZMod via the integer cast ring homomorphism.
      have hCast :
          ((M'^d' : ℤ) : ZMod N) = (M' : ZMod N) ^ d' := by
        simp
      -- Step 8.1.2: Combine with hPowFinal'.
      simpa [hCast] using hPowFinal'
    -- Step 8.2: Switch back to the language of congruences.
    exact (ZMod.intCast_eq_intCast_iff (M'^d') M N).1 hEq
  -- Step 9: Package the constructed d' together with the two required properties.
  -- Step 9.0: Upgrade the modular inverse to the required integer congruence.
  have hdEqNat :
      ((d' * d : ℕ) : ZMod φ) = ((1 : ℕ) : ZMod φ) := by
    -- Step 9.0.1: Reuse the equality established earlier over ℕ.
    simpa using hdMulNat
  have hdEq :
      ((d' * d : ℤ) : ZMod φ) = ((1 : ℤ) : ZMod φ) := by
    -- Step 9.0.2: Transfer the equality from ℕ to ℤ.
    simpa using hdEqNat
  have hdMod :
      (d' * d : ℤ) ≡ 1 [ZMOD φ] :=
    (ZMod.intCast_eq_intCast_iff _ _ _).1 hdEq
  -- Step 9.1: Report the modular inverse relation and the final congruence.
  exact ⟨d', hdMod, hFinal.symm⟩
