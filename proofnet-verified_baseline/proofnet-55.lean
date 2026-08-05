import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $|G|=1365$ then $G$ is not simple.
-/

/-Informal Proof

Since $|G|=1365=3.5.7.13$, $G$ has $13-$Sylow subgroup of order $13$. Now, we count the number of such subgroups. Let $n_{13}$ be the number of $13-$Sylow subgroup. Now $n_{13}=1+13k$ where $1+13k|3.5.7$. The choices for $k$ is $0$. Hence, there is a unique $13-$Sylow subgroup and hence is normal. so $G$ is not simple.
-/

theorem Dummit_Foote_exercise_4_5_20 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 1365) : ¬ IsSimpleGroup G := by
  classical
  /- Step 1: verify arithmetically that `1365` is squarefree
     (i.e. a product of pairwise distinct primes 3, 5, 7, and 13). -/
  have hSquarefree1365 : Squarefree 1365 := by
    -- Step 1.1: this is a concrete numeric fact, so we let `native_decide`
    -- check it by exhaustive computation.
    native_decide
  /- Step 2: transport the squarefreeness information from the number `1365`
     to the actual group `G` using the cardinality hypothesis `hG`. -/
  have hSquarefreeG : Squarefree (Nat.card G) := by
    -- Step 2.1: rewrite `Nat.card G` as `card G`, and then replace `card G`
    -- with `1365` via the given equality `hG`.
    simpa [Nat.card_eq_fintype_card, hG] using hSquarefree1365
  /- Step 3: a finite group whose order is squarefree is a Z-group,
     meaning that every Sylow subgroup is cyclic. -/
  have hZ : IsZGroup G := IsZGroup.of_squarefree (G := G) hSquarefreeG
  -- Step 3.1: register the Z-group structure as a typeclass instance so that
  -- subsequent steps can use it automatically.
  haveI : IsZGroup G := hZ
  /- Step 4: finite Z-groups are solvable, so we record that `G` is solvable. -/
  have hSolv : IsSolvable G := inferInstance
  /- Step 5: assume, for contradiction, that `G` is simple. -/
  intro hSimple
  -- Step 5.1: turn the simplicity hypothesis into a typeclass instance
  -- so that we can invoke lemmas stated under `[IsSimpleGroup G]`.
  haveI : IsSimpleGroup G := hSimple
  /- Step 6: in a simple group, solvability is equivalent to commutativity,
     so from `hSolv` we deduce that the multiplication on `G` is commutative. -/
  have hcomm : ∀ a b : G, a * b = b * a :=
    (IsSimpleGroup.comm_iff_isSolvable (G := G)).2 hSolv
  -- Step 6.1: register this commutativity as a typeclass instance so that
  -- we can treat `G` as an abelian (multiplicatively commutative) group.
  haveI : IsMulCommutative G := ⟨⟨hcomm⟩⟩
  /- Step 7: pick a Sylow 5-subgroup of `G`; it exists because 5 is prime
     and divides the order of `G`. -/
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  -- Step 7.1: choose a specific Sylow 5-subgroup using classical choice.
  let P5 : Sylow 5 G := Classical.choice (inferInstance : Nonempty (Sylow 5 G))
  /- Step 7.2: compute the order of `P5`. Since `|G| = 1365` and the exponent
     of 5 in its prime factorisation is 1, we must have `|P5| = 5`. -/
  have hfac5 : Nat.factorization (card G) 5 = 1 := by
    -- Step 7.2.1: compute the exponent of 5 in the factorisation of 1365 directly.
    have : Nat.factorization 1365 5 = 1 := by native_decide
    -- Step 7.2.2: transport this equality along the cardinality equality `hG`.
    simpa [hG] using this
  have hP5card : Fintype.card P5 = 5 := by
    -- Step 7.2.3: use the general formula for the order of a Sylow p-subgroup
    -- in terms of the factorisation of the group order.
    have h := (P5.card_eq_multiplicity (G := G))
    -- Here `h : Nat.card P5 = 5 ^ Nat.factorization (card G) 5`.
    have h' : Nat.card P5 = 5 ^ 1 := by
      -- Step 7.2.4: substitute the concrete exponent `1` we computed above.
      simpa [hfac5] using h
    -- Step 7.2.5: convert from `Nat.card` back to `Fintype.card` and simplify `5 ^ 1`.
    simpa [Nat.card_eq_fintype_card] using h'
  /- Step 7.3: show that `P5` is a nontrivial proper subgroup of `G`
     by comparing its order with `|G|`. -/
  have hP5_ne_bot : (P5 : Subgroup G) ≠ ⊥ := by
    -- Step 7.3.1: if `P5` were the trivial subgroup, its cardinality would be 1,
    -- contradicting `hP5card = 5`.
    intro h
    have := congrArg (fun H : Subgroup G => Fintype.card H) h
    -- The left-hand side becomes `Fintype.card P5 = 5`, while the right-hand
    -- side becomes `Fintype.card ⊥ = 1`.
    simp [hP5card] at this
  have hP5_ne_top : (P5 : Subgroup G) ≠ ⊤ := by
    -- Step 7.3.2: if `P5` were all of `G`, then `|G|` would be 5, again
    -- contradicting the given cardinality `|G| = 1365`.
    intro h
    have := congrArg (fun H : Subgroup G => Fintype.card H) h
    -- The right-hand side simplifies to `Fintype.card ⊤ = |G| = 1365`.
    simp [hG, hP5card] at this
  /- Step 8: in an abelian group, every subgroup is normal. Therefore the
     Sylow 5-subgroup `P5` is a nontrivial proper normal subgroup, which
     contradicts the simplicity of `G`. -/
  have hP5_normal : (P5 : Subgroup G).Normal := by
    -- Step 8.1: to show normality, we show invariance under conjugation.
    refine ⟨?_⟩
    intro x hx g
    -- Step 8.1.1: in an abelian group, conjugation is trivial:
    -- `g * x * g⁻¹ = x`.
    have hconj : g * x * g⁻¹ = x := by
      calc
        g * x * g⁻¹ = x * g * g⁻¹ := by
          -- rearrange using commutativity and associativity
          simp [mul_comm, mul_assoc]
        _ = x := by
          -- cancel `g * g⁻¹ = 1`.
          simp
    -- Step 8.1.2: use the equality `g * x * g⁻¹ = x` to transport membership.
    simpa [hconj] using hx
  -- Step 8.2: apply the definition of a simple group to the normal subgroup `P5`.
  have hBotOrTop := IsSimpleGroup.eq_bot_or_eq_top_of_normal (P5 : Subgroup G) hP5_normal
  -- Step 8.3: either possibility contradicts that `P5` is both nontrivial and proper.
  cases hBotOrTop with
  | inl h => exact hP5_ne_bot h
  | inr h => exact hP5_ne_top h
