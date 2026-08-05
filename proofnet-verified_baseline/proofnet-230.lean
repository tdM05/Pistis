import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $H$ has finite index $n$ then there is a normal subgroup $K$ of $G$ with $K \leq H$ and $|G: K| \leq n!$.
-/

/-Informal Proof

Solution: $G$ acts on the cosets $G / H$ by left multiplication. Let $\lambda: G \rightarrow S_{G / H}$ be the permutation representation induced by this action, and let $K$ be the kernel of the representation.
Now $K$ is normal in $G$, and $K \leq \operatorname{stab}_G(H)=H$. By the First Isomorphism Theorem, we have an injective group homomorphism $\bar{\lambda}: G / K \rightarrow S_{G / H}$. Since $\left|S_{G / H}\right|=n !$, we have $[G: K] \leq n !$.
-/

theorem Dummit_Foote_exercise_4_2_8 {G : Type*} [Group G] {H : Subgroup G}
  {n : ℕ} (hn : n > 0) (hH : H.index = n) :
  ∃ K ≤ H, K.Normal ∧ K.index ≤ n.factorial := by
  classical
  /- Step 1: Turn the hypothesis `n > 0` into concrete finite-index data for later use. -/
  have hn_ne_zero : n ≠ 0 := Nat.ne_of_gt hn
  /- Step 1.1: Transfer the nonzeroness from `n` to `H.index` so that the coset space `G ⧸ H`
    acquires a finite type structure. -/
  have hH_ne_zero : H.index ≠ 0 := by simpa [hH] using hn_ne_zero
  /- Step 1.2: Equip `G ⧸ H` with its induced `Fintype` structure coming from the previous step. -/
  have _ := H.fintypeOfIndexNeZero hH_ne_zero
  /- Step 2: Choose the candidate normal subgroup, namely the normal core of `H`. -/
  refine ⟨H.normalCore, ?_, ?_, ?_⟩
  · /- Step 2.1: By definition, the normal core is contained in the original subgroup. -/
    exact Subgroup.normalCore_le H
  · /- Step 2.2: The normal core is normal because it is constructed as an intersection of conjugates. -/
    exact inferInstance
  · /- Step 3: Bound the index of the normal core via the permutation action on cosets. -/
    /- Step 3.1: Introduce the permutation representation of `G` on `G ⧸ H`. -/
    let φ := MulAction.toPermHom G (G ⧸ H)
    /- Step 3.2: The kernel of this representation is exactly the normal core. -/
    have hker : H.normalCore = φ.ker := by
      simpa [φ] using (Subgroup.normalCore_eq_ker (H := H))
    /- Step 3.3: Express the desired index as the cardinality of the image of `φ`. -/
    have h_index_eq_card_range :
        H.normalCore.index = Nat.card φ.range := by
      have h1 : H.normalCore.index = Nat.card (G ⧸ φ.ker) := by
        simpa [hker] using (Subgroup.index_eq_card (φ.ker))
      have h2 : Nat.card (G ⧸ φ.ker) = Nat.card φ.range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
      exact h1.trans h2
    /- Step 3.4: The range embeds into the full permutation group, giving an upper bound on its size. -/
    have h_range_le :
        Nat.card φ.range ≤ Nat.card (Equiv.Perm (G ⧸ H)) := by
      classical
      have h_card_le :
          Fintype.card φ.range ≤ Fintype.card (Equiv.Perm (G ⧸ H)) :=
        Fintype.card_le_of_injective (fun x : φ.range => (x : Equiv.Perm (G ⧸ H)))
          Subtype.coe_injective
      simpa [Nat.card_eq_fintype_card] using h_card_le
    /- Step 3.5: Identify the size of the coset space with `n` using the hypothesis on the index. -/
    have h_card_cosets_nat : Nat.card (G ⧸ H) = n := by
      have := (Subgroup.index_eq_card (H := H)).symm
      simpa [hH] using this
    have h_card_cosets :
        Fintype.card (G ⧸ H) = n := by
      simpa [Nat.card_eq_fintype_card] using h_card_cosets_nat
    /- Step 3.6: Combine all previous comparisons to obtain the factorial bound. -/
    exact
      calc
        H.normalCore.index
            = Nat.card φ.range := h_index_eq_card_range
        _ ≤ Nat.card (Equiv.Perm (G ⧸ H)) := h_range_le
        _ = Fintype.card (Equiv.Perm (G ⧸ H)) := by
              simp [Nat.card_eq_fintype_card]
        _ = Nat.factorial (Fintype.card (G ⧸ H)) := by
              simpa using (Fintype.card_perm (α := G ⧸ H))
        _ = n.factorial := by simp [h_card_cosets]



/-
This trivial proof demonstrates why the original formalization is weaker than
the informal statement. When G is infinite, `Subgroup.index` (defined as
`Nat.card (G ⧸ K)`) returns 0 for any subgroup K such that G ⧸ K is infinite.
In particular, `(⊥ : Subgroup G).index = Nat.card G = 0` for infinite G.

The witness K = ⊥ satisfies:
  - ⊥ ≤ H: trivially, the trivial subgroup is contained in any subgroup.
  - ⊥.Normal: the trivial subgroup is always normal.
  - ⊥.index ≤ n!: since ⊥.index = 0 and 0 ≤ n! for any n.

No hypothesis (`hn`, `hH`) is used. The proof goes through for ANY infinite
group G, any subgroup H, and any n > 0 — without doing any group theory.

This is clearly not what the informal statement intends: informally,
|G : K| = |G| = ∞ > n!, so K = ⊥ should NOT be a valid witness.
The mismatch arises because Mathlib encodes "infinite index" as 0,
which accidentally satisfies the ≤ bound.
-/
theorem Dummit_Foote_exercise_4_2_8_trivial {G : Type*} [Group G] [Infinite G] {H : Subgroup G}
  {n : ℕ} (_hn : n > 0) (_hH : H.index = n) :
  ∃ K ≤ H, K.Normal ∧ K.index ≤ n.factorial := by
  refine ⟨⊥, bot_le, inferInstance, ?_⟩
  rw [Subgroup.index_bot, Nat.card_eq_zero_of_infinite]
  exact Nat.zero_le _

/-
The original formalization is weaker than the informal statement.

In Mathlib, `Subgroup.index` returns 0 for subgroups of infinite index
(since `Nat.card` of an infinite type is 0). This means any normal subgroup
K ≤ H with infinite index trivially satisfies `K.index ≤ n.factorial`
(as 0 ≤ n!). The theorem above demonstrates this: when G is infinite,
the trivial subgroup ⊥ witnesses the existential without doing any real
mathematics.

The informal statement implicitly requires K to have *finite* index
bounded by n!. The corrected formalization adds `0 < K.index` to ensure
the index is genuinely finite.
-/

theorem Dummit_Foote_exercise_4_2_8_corrected {G : Type*} [Group G] {H : Subgroup G}
  {n : ℕ} (hn : n > 0) (hH : H.index = n) :
  ∃ K ≤ H, K.Normal ∧ 0 < K.index ∧ K.index ≤ n.factorial := by
  classical
  -- Step 1: Derive finite-index data from the hypothesis.
  have hn_ne_zero : n ≠ 0 := Nat.ne_of_gt hn
  -- Step 1.1: Transfer nonzeroness to H.index.
  have hH_ne_zero : H.index ≠ 0 := by simpa [hH] using hn_ne_zero
  -- Step 1.2: Equip the coset space G ⧸ H with a Fintype instance.
  have _ := H.fintypeOfIndexNeZero hH_ne_zero
  -- Step 2: Choose K = H.normalCore, the largest normal subgroup contained in H.
  refine ⟨H.normalCore, ?_, ?_, ?_, ?_⟩
  · -- Step 2.1: The normal core is contained in H by definition.
    exact Subgroup.normalCore_le H
  · -- Step 2.2: The normal core is normal.
    exact inferInstance
  · -- Step 3: Prove 0 < H.normalCore.index (i.e., the index is genuinely finite and positive).
    -- Step 3.1: The normal core's index divides n! (shown below), so it suffices to show it's nonzero.
    -- Step 3.2: Since H has finite index, the coset space G ⧸ H is finite.
    --   The permutation representation φ : G →* Perm(G ⧸ H) has ker = normalCore.
    --   The quotient G / ker injects into Perm(G ⧸ H), which is finite.
    --   Hence G / normalCore is finite, so normalCore.index ≠ 0.
    let φ := MulAction.toPermHom G (G ⧸ H)
    have hker : H.normalCore = φ.ker := by
      simpa [φ] using (Subgroup.normalCore_eq_ker (H := H))
    -- Step 3.3: Express the index as the cardinality of the range of φ.
    have h_index_eq_card_range :
        H.normalCore.index = Nat.card φ.range := by
      have h1 : H.normalCore.index = Nat.card (G ⧸ φ.ker) := by
        simpa [hker] using (Subgroup.index_eq_card (φ.ker))
      have h2 : Nat.card (G ⧸ φ.ker) = Nat.card φ.range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
      exact h1.trans h2
    -- Step 3.4: The range is a subgroup of a finite group, hence has positive cardinality.
    have h_range_pos : 0 < Nat.card φ.range := by
      have : Fintype φ.range := inferInstance
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos
    -- Step 3.5: Combine to get positivity of the index.
    omega
  · -- Step 4: Prove H.normalCore.index ≤ n.factorial via the permutation representation.
    -- Step 4.1: Introduce the permutation representation.
    let φ := MulAction.toPermHom G (G ⧸ H)
    -- Step 4.2: The kernel is the normal core.
    have hker : H.normalCore = φ.ker := by
      simpa [φ] using (Subgroup.normalCore_eq_ker (H := H))
    -- Step 4.3: Express the index as the cardinality of the range.
    have h_index_eq_card_range :
        H.normalCore.index = Nat.card φ.range := by
      have h1 : H.normalCore.index = Nat.card (G ⧸ φ.ker) := by
        simpa [hker] using (Subgroup.index_eq_card (φ.ker))
      have h2 : Nat.card (G ⧸ φ.ker) = Nat.card φ.range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
      exact h1.trans h2
    -- Step 4.4: The range embeds into the full permutation group.
    have h_range_le :
        Nat.card φ.range ≤ Nat.card (Equiv.Perm (G ⧸ H)) := by
      have h_card_le :
          Fintype.card φ.range ≤ Fintype.card (Equiv.Perm (G ⧸ H)) :=
        Fintype.card_le_of_injective (fun x : φ.range => (x : Equiv.Perm (G ⧸ H)))
          Subtype.coe_injective
      simpa [Nat.card_eq_fintype_card] using h_card_le
    -- Step 4.5: Identify the cardinality of the coset space with n.
    have h_card_cosets :
        Fintype.card (G ⧸ H) = n := by
      have h_card_cosets_nat : Nat.card (G ⧸ H) = n := by
        have := (Subgroup.index_eq_card (H := H)).symm
        simpa [hH] using this
      simpa [Nat.card_eq_fintype_card] using h_card_cosets_nat
    -- Step 4.6: Chain the inequalities to obtain the factorial bound.
    calc
      H.normalCore.index
          = Nat.card φ.range := h_index_eq_card_range
      _ ≤ Nat.card (Equiv.Perm (G ⧸ H)) := h_range_le
      _ = Fintype.card (Equiv.Perm (G ⧸ H)) := by
            simp [Nat.card_eq_fintype_card]
      _ = Nat.factorial (Fintype.card (G ⧸ H)) := by
            simpa using (Fintype.card_perm (α := G ⧸ H))
      _ = n.factorial := by simp [h_card_cosets]
