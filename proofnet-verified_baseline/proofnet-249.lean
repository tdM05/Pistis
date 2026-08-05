import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $q \in \mathbb{Z}$ be a prime with $q \equiv 3 \bmod 4$. Prove that the quotient ring $\mathbb{Z}[i] /(q)$ is a field with $q^{2}$ elements.
-/

/-Informal Proof

The division algorithm gives us that every element of $\mathbb{Z}[i] /\langle q\rangle$ is represented by an element $a+b i$ such that $0 \leq a, b<q$. Each such choice is distinct since if $a_1+b_1 i+\langle q\rangle=a_2+b_2 i+\langle q\rangle$, then $\left(a_1-a_2\right)+\left(b_1-b_2\right) i$ is divisible by $q$, so $a_1 \equiv a_2 \bmod q$ and $b_1 \equiv b_2 \bmod q$. So $\mathbb{Z}[i] /\langle q\rangle$ has order $q^2$.

Since $q \equiv 3 \bmod 4, q$ is irreducible, hence prime in $\mathbb{Z}[i]$. Therefore $\langle q\rangle$ is a prime ideal in $\mathbb{Z}[i]$, and so $\mathbb{Z}[i] /\langle q\rangle$ is an integral domain. So $\mathbb{Z}[i] /\langle q\rangle$ is a field.
-/

/-
=============================================================================
ORIGINAL STATEMENT (KEPT WITH SORRY AS REQUIRED)
=============================================================================
-/
theorem Dummit_Foote_exercise_8_3_6b {q : ℕ} (hq0 : q.Prime)
  (hq1 : q ≡ 3 [ZMOD 4]) {R : Type} [Ring R]
  (hR : R = (GaussianInt ⧸ span ({↑q} : Set GaussianInt))) :
  IsField R ∧ ∃ finR : Fintype R, @card R finR = q^2 := by
  sorry

/-
=============================================================================
EXPLANATION OF THE PROBLEM WITH THE ORIGINAL STATEMENT
=============================================================================

The original theorem statement is PROBLEMATIC for the following reasons:

1. FLAWED FORMALIZATION: The statement introduces R as an arbitrary Type with a
   Ring structure, then provides a hypothesis hR : R = (GaussianInt ⧸ span ...)

2. TYPE EQUALITY ISSUE: In dependent type theory (which Lean uses), the equality
   R = (GaussianInt ⧸ span ...) is a PROPOSITIONAL equality between types.
   This is fundamentally different from saying R is defined AS this quotient type.

3. STRUCTURE MISMATCH: Even if R equals the quotient type, the Ring structure
   on R (given by [Ring R]) may not match the quotient ring structure.
   The hypothesis hR only tells us the types are equal, not that the
   algebraic structures are the same.

4. INSTANCE TRANSFER PROBLEM: To prove IsField R, we would need to transfer
   the field structure from the quotient to R using type equality transport
   (Eq.rec/subst), but this doesn't work well with type class inference.
   After substitution, the Ring instance inst✝ on R does NOT become the
   canonical quotient ring instance Quotient.commRing.

5. THE MATHEMATICS IS CORRECT: The underlying mathematical statement is true:
   Z[i]/(q) IS a field with q² elements when q is prime and q ≡ 3 (mod 4).
   The issue is purely with the formalization, not the mathematics.

The statement should instead directly assert properties of the quotient type,
not of an arbitrary R that happens to equal it propositionally.
-/

/-
=============================================================================
CORRECTED STATEMENT AND FULL PROOF
=============================================================================

The correct formalization states properties directly for the quotient ring:
-/

-- ============================================================================
-- HELPER DEFINITIONS AND LEMMAS
-- ============================================================================

-- Step 1: Define the ideal (q) in the Gaussian integers for convenience
abbrev idealQ (q : ℕ) : Ideal GaussianInt := span ({↑q} : Set GaussianInt)

-- Step 2: Define the quotient type for convenience
abbrev quotientQ (q : ℕ) := GaussianInt ⧸ idealQ q

-- ============================================================================
-- PART 1: PROVING THE QUOTIENT IS A FIELD
-- ============================================================================

-- Step 3: Convert ZMOD congruence to natural number mod
-- If q ≡ 3 [ZMOD 4], then q % 4 = 3
lemma zmod_to_nat_mod {q : ℕ} (hq1 : q ≡ 3 [ZMOD 4]) : q % 4 = 3 := by
  -- Step 3.1: Unfold the ZMOD definition
  unfold Int.ModEq at hq1
  -- Step 3.2: Use the relationship between Int and Nat mod
  have h : (q : ℤ) % 4 = 3 := by omega
  have hnat : (q : ℤ) % 4 = (q % 4 : ℕ) := Int.natCast_mod q 4
  -- Step 3.3: Conclude
  omega

-- Step 4: Prove q is prime in GaussianInt when q ≡ 3 (mod 4)
-- Key fact: A prime p is prime in Z[i] iff p ≡ 3 (mod 4)
lemma q_prime_in_gaussian {q : ℕ} (hq0 : q.Prime) (hq1 : q ≡ 3 [ZMOD 4]) :
    Prime (q : GaussianInt) := by
  -- Step 4.1: Convert ZMOD to nat mod
  have qmod : q % 4 = 3 := zmod_to_nat_mod hq1
  -- Step 4.2: Register q as a prime fact for typeclass inference
  haveI : Fact (Nat.Prime q) := ⟨hq0⟩
  -- Step 4.3: Apply the theorem from Mathlib: p is prime in Z[i] iff p % 4 = 3
  exact GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime q |>.mpr qmod

-- Step 5: The ideal (q) is maximal when q is prime in GaussianInt
-- In a PID, ideals generated by irreducible elements are maximal
lemma idealQ_maximal {q : ℕ} (hq0 : q.Prime) (hq1 : q ≡ 3 [ZMOD 4]) :
    (idealQ q).IsMaximal := by
  -- Step 5.1: Get that q is prime in GaussianInt
  have hp : Prime (q : GaussianInt) := q_prime_in_gaussian hq0 hq1
  -- Step 5.2: Prime elements are irreducible in integral domains
  have hirr : Irreducible (q : GaussianInt) := hp.irreducible
  -- Step 5.3: In a PID, span of irreducible is maximal
  -- GaussianInt is a PID (it's a Euclidean domain)
  exact PrincipalIdealRing.isMaximal_of_irreducible hirr

-- Step 6: The quotient is a field
-- Quotient by maximal ideal is a field
lemma quotientQ_is_field {q : ℕ} (hq0 : q.Prime) (hq1 : q ≡ 3 [ZMOD 4]) :
    IsField (quotientQ q) := by
  -- Step 6.1: Get that the ideal is maximal
  have hmax : (idealQ q).IsMaximal := idealQ_maximal hq0 hq1
  -- Step 6.2: Apply the characterization: maximal ideal ↔ quotient is field
  rw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact hmax

-- ============================================================================
-- PART 2: PROVING THE QUOTIENT HAS CARDINALITY q²
-- ============================================================================

-- Step 7: Characterize membership in span {q}
-- z ∈ span {q} iff q | z.re and q | z.im
lemma mem_idealQ_iff (q : ℕ) (z : GaussianInt) :
    z ∈ idealQ q ↔ (q : ℤ) ∣ z.re ∧ (q : ℤ) ∣ z.im := by
  -- Step 7.1: Rewrite using span_singleton membership
  rw [mem_span_singleton]
  constructor
  -- Step 7.2: Forward direction: if q | z, then q | z.re and q | z.im
  · intro ⟨c, hc⟩
    constructor
    -- Step 7.2.1: Show q | z.re
    · use c.re
      have := congrArg Zsqrtd.re hc
      simp only [Zsqrtd.re_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast] at this
      linarith
    -- Step 7.2.2: Show q | z.im
    · use c.im
      have := congrArg Zsqrtd.im hc
      simp only [Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast] at this
      linarith
  -- Step 7.3: Backward direction: if q | z.re and q | z.im, then q | z
  · intro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    use ⟨a, b⟩
    ext
    -- Step 7.3.1: Real part
    · simp only [Zsqrtd.re_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast]
      linarith
    -- Step 7.3.2: Imaginary part
    · simp only [Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast]
      linarith

-- Step 8: Show [0] ≠ [1] in the quotient (quotient is nontrivial)
lemma quotientQ_nontrivial {q : ℕ} (hq0 : q.Prime) : (0 : quotientQ q) ≠ 1 := by
  -- Step 8.1: Assume for contradiction [0] = [1]
  intro h
  -- Step 8.2: This means 0 - 1 = -1 ∈ idealQ q
  have h1 : (Ideal.Quotient.mk (idealQ q)) 0 = (Ideal.Quotient.mk (idealQ q)) 1 := by
    simp only [map_zero, map_one]; exact h
  rw [Ideal.Quotient.eq] at h1
  -- Step 8.3: So 1 ∈ idealQ q (since 0 - 1 = -1 and -(-1) = 1)
  have h1' : (1 : GaussianInt) ∈ idealQ q := by
    have hn : -(0 - 1) ∈ idealQ q := Submodule.neg_mem _ h1
    simp only [neg_sub, sub_zero] at hn
    exact hn
  -- Step 8.4: This means idealQ q = ⊤
  have htop : idealQ q = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact h1'
  -- Step 8.5: But span {q} ≠ ⊤ for prime q > 1
  have hne : idealQ q ≠ ⊤ := by
    intro heq
    rw [span_singleton_eq_top] at heq
    -- heq : IsUnit q
    have : IsUnit (q : GaussianInt) := heq
    rw [Zsqrtd.isUnit_iff_norm_isUnit] at this
    -- norm(q) = q² should be a unit in ℤ, but q² is not ±1 for prime q
    have hnorm : Zsqrtd.norm (q : GaussianInt) = (q : ℤ) * q := Zsqrtd.norm_natCast q
    rw [hnorm, Int.isUnit_iff] at this
    have hq_pos : 1 < q := hq0.one_lt
    -- q * q = 1 or q * q = -1 is impossible for q ≥ 2
    rcases this with h1 | h2
    · have : (q : ℤ) * q ≥ 4 := by nlinarith
      omega
    · have : (q : ℤ) * q ≥ 4 := by nlinarith
      omega
  exact hne htop

-- Step 9: Helper lemma for converting leftRel to ideal membership
lemma leftRel_to_mem (q : ℕ) [NeZero q] (a b : GaussianInt)
    (hab : @QuotientAddGroup.leftRel GaussianInt _
           (Submodule.toAddSubgroup (idealQ q)) a b) :
    a - b ∈ idealQ q := by
  -- Step 9.1: Unfold the leftRel definition
  rw [QuotientAddGroup.leftRel_apply] at hab
  -- Step 9.2: hab says -a + b ∈ I, which is b - a ∈ I
  have h1 : -a + b = b - a := by ring
  rw [h1] at hab
  -- Step 9.3: Convert membership
  have h2 : b - a ∈ (idealQ q : Set GaussianInt) := hab
  -- Step 9.4: Since I is a submodule, -(b-a) = a - b ∈ I
  have h3 : -(b - a) ∈ idealQ q := Submodule.neg_mem _ h2
  simp only [neg_sub] at h3
  exact h3

-- Step 10: Define the map from quotient to ZMod q × ZMod q
variable (q : ℕ) [NeZero q]

noncomputable def quotientToZModProd :
    quotientQ q → ZMod q × ZMod q :=
  Quotient.lift (fun z => ((z.re : ZMod q), (z.im : ZMod q))) (by
    intro a b hab
    -- Step 10.1: Convert ≈ to ideal membership
    have hmem : a - b ∈ idealQ q := leftRel_to_mem q a b hab
    rw [mem_idealQ_iff] at hmem
    obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := hmem
    ext
    -- Step 10.2: Real parts are equal mod q
    · have h : a.re - b.re = q * c := by
        have : (a - b).re = a.re - b.re := rfl
        rw [← this]; exact hc
      rw [← sub_eq_zero, ← Int.cast_sub, h, Int.cast_mul, Int.cast_natCast,
          ZMod.natCast_self, zero_mul]
    -- Step 10.3: Imaginary parts are equal mod q
    · have h : a.im - b.im = q * d := by
        have : (a - b).im = a.im - b.im := rfl
        rw [← this]; exact hd
      rw [← sub_eq_zero, ← Int.cast_sub, h, Int.cast_mul, Int.cast_natCast,
          ZMod.natCast_self, zero_mul])

-- Step 11: Define the map from ZMod q × ZMod q to quotient
def zModProdToQuotient :
    ZMod q × ZMod q → quotientQ q :=
  fun p => Ideal.Quotient.mk _ ⟨(p.1.val : ℤ), (p.2.val : ℤ)⟩

-- Step 12: Prove these maps form a bijection (left inverse)
lemma quotient_zmod_left_inv (p : ZMod q × ZMod q) :
    quotientToZModProd q (zModProdToQuotient q p) = p := by
  -- Step 12.1: Unfold definitions
  unfold zModProdToQuotient quotientToZModProd
  -- Step 12.2: Show coordinates match
  ext
  · -- Step 12.2.1: First coordinate: ((p.1.val : ℤ) : ZMod q) = p.1
    change ((p.1.val : ℤ) : ZMod q) = p.1
    rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
  · -- Step 12.2.2: Second coordinate: ((p.2.val : ℤ) : ZMod q) = p.2
    change ((p.2.val : ℤ) : ZMod q) = p.2
    rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]

-- Step 13: Prove these maps form a bijection (right inverse)
lemma quotient_zmod_right_inv (x : quotientQ q) :
    zModProdToQuotient q (quotientToZModProd q x) = x := by
  -- Step 13.1: Get a representative
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- Step 13.2: Unfold definitions
  unfold quotientToZModProd zModProdToQuotient
  -- Step 13.3: Show the representatives differ by an element of the ideal
  rw [Ideal.Quotient.eq]
  rw [mem_idealQ_iff]
  constructor
  -- Step 13.4: Real part divisibility: show q | ((z.re : ZMod q).val - z.re)
  · -- Step 13.4.1: The key fact: (z.re : ZMod q).val = z.re % q
    have hval : ((z.re : ZMod q).val : ℤ) = z.re % (q : ℤ) := ZMod.val_intCast z.re
    -- Step 13.4.2: We have z.re % q + q * (z.re / q) = z.re
    have hdiv : z.re % (q : ℤ) + (q : ℤ) * (z.re / (q : ℤ)) = z.re := Int.emod_add_mul_ediv z.re q
    -- Step 13.4.3: Use -(z.re / q) as the witness
    use -(z.re / q)
    -- Step 13.4.4: Compute the difference
    show (⟨(z.re : ZMod q).val, (z.im : ZMod q).val⟩ : GaussianInt).re - z.re = q * (-(z.re / q))
    rw [hval]
    linarith
  -- Step 13.5: Imaginary part divisibility
  · -- Step 13.5.1: The key fact: (z.im : ZMod q).val = z.im % q
    have hval : ((z.im : ZMod q).val : ℤ) = z.im % (q : ℤ) := ZMod.val_intCast z.im
    -- Step 13.5.2: We have z.im % q + q * (z.im / q) = z.im
    have hdiv : z.im % (q : ℤ) + (q : ℤ) * (z.im / (q : ℤ)) = z.im := Int.emod_add_mul_ediv z.im q
    -- Step 13.5.3: Use -(z.im / q) as the witness
    use -(z.im / q)
    -- Step 13.5.4: Compute the difference
    show (⟨(z.re : ZMod q).val, (z.im : ZMod q).val⟩ : GaussianInt).im - z.im = q * (-(z.im / q))
    rw [hval]
    linarith

-- Step 14: The maps form an equivalence
noncomputable def quotientEquivZModProd :
    quotientQ q ≃ ZMod q × ZMod q where
  toFun := quotientToZModProd q
  invFun := zModProdToQuotient q
  left_inv := quotient_zmod_right_inv q
  right_inv := quotient_zmod_left_inv q

-- Step 15: Define Fintype instance for the quotient
noncomputable instance quotientQFintype : Fintype (quotientQ q) :=
  Fintype.ofEquiv (ZMod q × ZMod q) (quotientEquivZModProd q).symm

-- Step 16: Prove the cardinality equals q²
lemma quotientQ_card_eq_sq : @Fintype.card (quotientQ q) (quotientQFintype q) = q ^ 2 := by
  -- Step 16.1: Use that card is preserved by equivalence
  rw [Fintype.card_congr (quotientEquivZModProd q)]
  -- Step 16.2: Card of product is product of cards
  rw [Fintype.card_prod]
  -- Step 16.3: Card of ZMod q is q
  simp only [ZMod.card]
  -- Step 16.4: Conclude q * q = q²
  ring

-- ============================================================================
-- NEGATION OF THE ORIGINAL THEOREM
-- ============================================================================

/-
The original statement is unprovable because `[Ring R]` is an arbitrary ring
structure on R, and `hR : R = Q` does not force it to be the canonical quotient
ring.  For q = 3 we can transport a non-field ring structure (from
`ZMod 3 × ZMod 3`) onto Q via `quotientEquivZModProd 3`, producing an R and
Ring R with R = Q but IsField R false.

We wrap the quotient in an opaque `def Q3` to avoid typeclass ambiguity with
the canonical `CommRing` instance on the quotient — otherwise Lean's `whnf`
diverges resolving `MulEquiv.isField`'s instance arguments.
-/
/-- Opaque alias of the quotient type for q = 3.  Using a `def` (rather than
`abbrev` or a direct expression) hides the canonical `CommRing` instance from
typeclass resolution, so we can attach a non-field `Ring` structure without
ambiguity. -/
private def Q3 : Type :=
  GaussianInt ⧸ span ({↑(3 : ℕ)} : Set GaussianInt)

private noncomputable instance : Ring Q3 :=
  haveI : NeZero (3 : ℕ) := ⟨by decide⟩
  (quotientEquivZModProd 3).ring

theorem Dummit_Foote_exercise_8_3_6b_neg :
    ¬ (∀ {q : ℕ} (_ : q.Prime) (_ : q ≡ 3 [ZMOD 4])
        {R : Type} [Ring R]
        (_ : R = (GaussianInt ⧸ span ({↑q} : Set GaussianInt))),
        IsField R ∧ ∃ finR : Fintype R, @card R finR = q^2) := by
  intro h
  have hp : Nat.Prime 3 := by decide
  have hm : (3 : ℕ) ≡ 3 [ZMOD 4] := by decide
  haveI : NeZero (3 : ℕ) := ⟨by decide⟩
  -- `Q3 = GaussianInt ⧸ span {↑3}` definitionally, but typeclass resolution
  -- uses the non-field Ring instance attached to `Q3`, not the canonical one.
  obtain ⟨hF, _⟩ := @h 3 hp hm Q3 _ rfl
  -- Transfer `IsField` across the equivalence `Q3 ≃ ZMod 3 × ZMod 3`.
  let e : Q3 ≃ ZMod 3 × ZMod 3 := quotientEquivZModProd 3
  have h_field : IsField (ZMod 3 × ZMod 3) :=
    MulEquiv.isField hF e.ringEquiv.symm.toMulEquiv
  -- Contradiction: `(1, 0)` has no inverse in `ZMod 3 × ZMod 3`.
  have h10_ne : ((1 : ZMod 3), (0 : ZMod 3)) ≠ 0 := by decide
  obtain ⟨c, hc⟩ := h_field.mul_inv_cancel h10_ne
  -- `(1, 0) * c = 1` in `ZMod 3 × ZMod 3` forces `0 = 1` in the second
  -- component, which is false.
  have hsnd := congrArg Prod.snd hc
  simp at hsnd

-- ============================================================================
-- CORRECTED THEOREM
-- ============================================================================

/-
The corrected statement directly asserts properties of the quotient ring:
-/
theorem Dummit_Foote_exercise_8_3_6b_corrected {q : ℕ} (hq0 : q.Prime) (hq1 : q ≡ 3 [ZMOD 4]) :
    IsField (GaussianInt ⧸ span ({↑q} : Set GaussianInt)) ∧
    ∃ finR : Fintype (GaussianInt ⧸ span ({↑q} : Set GaussianInt)),
      @Fintype.card _ finR = q ^ 2 := by
  -- Step 1: Register NeZero q for the cardinality computation
  haveI : NeZero q := ⟨hq0.ne_zero⟩
  constructor
  -- Part 1: The quotient is a field
  · exact quotientQ_is_field hq0 hq1
  -- Part 2: There exists a Fintype instance with card = q²
  · use quotientQFintype q
    exact quotientQ_card_eq_sq q
