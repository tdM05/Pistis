import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that $\mathbb{Q}$ has no proper subgroups of finite index.
-/

/-Informal Proof

Solution: We begin with a lemma.
Lemma: If $D$ is a divisible abelian group, then no proper subgroup of $D$ has finite index.
Proof: We saw previously that no finite group is divisible and that every proper quotient $D / A$ of a divisible group is divisible; thus no proper quotient of a divisible group is finite. Equivalently, $[D: A]$ is not finite.
Because $\mathbb{Q}$ and $\mathbb{Q} / \mathbb{Z}$ are divisible, the conclusion follows.
-/

-- Step 1: Prove that every finite divisible additive group is trivial, which will power the main argument.
lemma subsingleton_of_finite_divisibleBy_nat {G : Type*} [AddCommGroup G] [Finite G]
    [DivisibleBy G ℕ] : Subsingleton G := by
  -- Step 1.1: Work classically and convert the `Finite` hypothesis into a `Fintype` instance to talk about `Fintype.card`.
  classical
  let _ := Fintype.ofFinite G
  -- Step 1.2: Show that every element is zero by exploiting divisibility and the finite cardinality.
  have aux : ∀ g : G, g = 0 := by
    intro g
    -- Step 1.2.1: Record that the group order, viewed as a natural number, is nonzero.
    have h_card_nat : (Fintype.card G : ℕ) ≠ 0 :=
      Fintype.card_ne_zero
    -- Step 1.2.2: Use divisibility to express `g` as a multiple of an element whose natural multiple is `g`.
    have h_div :
        (Fintype.card G) • DivisibleBy.div g (Fintype.card G) = g :=
      DivisibleBy.div_cancel (A := G) (α := ℕ) (a := g)
        (n := Fintype.card G) h_card_nat
    -- Step 1.2.3: Finite additive groups are killed by their cardinality, so this multiple must be zero.
    have h_mul_zero :
        (Fintype.card G) • DivisibleBy.div g (Fintype.card G) = 0 := by
      exact card_nsmul_eq_zero (G := G)
          (x := DivisibleBy.div g (Fintype.card G))
    -- Step 1.2.4: Combine the previous two facts to conclude that `g` itself is zero.
    simpa [h_div] using h_mul_zero
  -- Step 1.3: Any two elements coincide because they both equal zero.
  refine ⟨fun g h => ?_⟩
  have hg : g = 0 := aux g
  have hh : h = 0 := aux h
  simp [hg, hh]

theorem Dummit_Foote_exercise_3_2_21a (H : AddSubgroup ℚ) (hH : H ≠ ⊤) : H.index = 0 := by
  -- Step 2: Assume towards a contradiction that the index is nonzero, i.e. `H` has finite index.
  classical
  haveI : DivisibleBy ℚ ℕ := AddGroup.divisibleByNatOfDivisibleByInt (A := ℚ)
  by_contra hIndex
  -- Step 2.1: Translate the nonzero index hypothesis into the `FiniteIndex` structure.
  have hFiniteIndex : H.FiniteIndex :=
    (AddSubgroup.finiteIndex_iff).2 hIndex
  -- Step 2.2: Record that the quotient `ℚ ⧸ H` is finite because `H` has finite index.
  have hFiniteQuot : Finite (ℚ ⧸ H) :=
    (AddSubgroup.finiteIndex_iff_finite_quotient).1 hFiniteIndex
  -- Step 2.3: Upgrade the finiteness proof and the divisibility fact to typeclass instances for the quotient.
  haveI : Finite (ℚ ⧸ H) := hFiniteQuot
  haveI : DivisibleBy (ℚ ⧸ H) ℕ := QuotientAddGroup.divisibleBy (A := ℚ) (B := H)
  -- Step 2.4: The auxiliary lemma now shows that every coset collapses to a single point.
  have hSubsingleton :
      Subsingleton (ℚ ⧸ H) :=
    subsingleton_of_finite_divisibleBy_nat (G := ℚ ⧸ H)
  -- Step 2.5: Use the singleton property to prove that all rationals lie in `H`.
  have hMem : ∀ x : ℚ, x ∈ H := by
    intro x
    -- Step 2.5.1: Any coset equals the zero coset in a subsingleton quotient.
    have hx :
        (QuotientAddGroup.mk x : ℚ ⧸ H) = 0 :=
      Subsingleton.elim _ _
    -- Step 2.5.2: Translate the equality of cosets into membership in `H`.
    have hxMem : x - (0 : ℚ) ∈ H :=
      (QuotientAddGroup.eq_iff_sub_mem (N := H) (x := x) (y := 0)).1
        (by simpa using hx)
    -- Step 2.5.3: Simplify the difference to conclude that `x` itself lies in `H`.
    simpa using hxMem
  -- Step 2.6: Conclude that `H` contains every element and is therefore the whole group.
  have hTop : H = ⊤ :=
    le_antisymm le_top fun x _ => hMem x
  exact hH hTop
