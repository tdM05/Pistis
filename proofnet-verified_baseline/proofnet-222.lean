import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

A subgroup $M$ of a group $G$ is called a maximal subgroup if $M \neq G$ and the only subgroups of $G$ which contain $M$ are $M$ and $G$. Prove that if $H$ is a proper subgroup of the finite group $G$ then there is a maximal subgroup of $G$ containing $H$.
-/

/-Informal Proof

If $H$ is maximal, then we are done. If $H$ is not maximal, then there is a subgroup $K_1$ of $G$ such that $H<K_1<G$. If $K_1$ is maximal, we are done. But if $K_1$ is not maximal, there is a subgroup $K_2$ with $H<K_1<K_2<G$. If $K_2$ is maximal, we are done, and if not, keep repeating the procedure. Since $G$ is finite, this process must eventually come to an end, so that $K_n$ is maximal for some positive integer $n$. Then $K_n$ is a maximal subgroup containing $H$.
-/

theorem Dummit_Foote_exercise_2_4_16a {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
  (hH : H ≠ ⊤) :
  ∃ M : Subgroup G, M ≠ ⊤ ∧
  (∀ K : Subgroup G, M ≤ K → K = M ∨ K = ⊤) ∧
  H ≤ M := by
  classical
  -- Step 1: Encode "proper supergroups of `H`" via a predicate on subgroup cardinalities.
  let P : ℕ → Prop :=
    fun k => ∃ K : Subgroup G, H ≤ K ∧ K ≠ ⊤ ∧ Fintype.card ↥K = k
  -- Step 1.1: Any subgroup injects into `G`, so its size is bounded above by `|G|`.
  have hBound : ∀ K : Subgroup G, Fintype.card ↥K ≤ Fintype.card G := by
    intro K
    refine Fintype.card_le_of_injective (fun k : K => (k : G)) ?_
    intro x y hxy
    ext
    simpa using hxy
  -- Step 1.2: The subgroup `H` itself witnesses the predicate and is bounded by `|G|`.
  have hWitness : P (Fintype.card ↥H) := ⟨H, le_rfl, hH, rfl⟩
  have hWitnessBound : Fintype.card ↥H ≤ Fintype.card G := hBound H
  -- Step 2: Use `Nat.findGreatest` to extract a subgroup `M` with maximal size among the witnesses.
  set n := Nat.findGreatest P (Fintype.card G) with hn
  have hPn : P n := by
    have := Nat.findGreatest_spec (P := P) (m := Fintype.card ↥H) (n := Fintype.card G)
        hWitnessBound hWitness
    simpa [n] using this
  -- Step 2.1: Unpack the predicate to obtain the desired subgroup `M`.
  rcases hPn with ⟨M, hHM, hMproper, hMcard⟩
  refine ⟨M, hMproper, ?_, hHM⟩
  -- Step 3: Prove that `M` is maximal among proper subgroups containing `H`.
  intro K hMK
  -- Step 3.1: If `K = ⊤`, we are immediately done.
  by_cases hKtop : K = ⊤
  · exact Or.inr hKtop
  -- Step 3.2: Otherwise, `K` is still proper and contains `H`.
  · have hHK : H ≤ K := hHM.trans hMK
    have hPK : P (Fintype.card ↥K) := ⟨K, hHK, hKtop, rfl⟩
    have hBoundK : Fintype.card ↥K ≤ Fintype.card G := hBound K
    -- Step 3.3: Maximality of `n` forces `|K| ≤ |M|`.
    have hLeN : Fintype.card ↥K ≤ n := by
      simpa [n] using Nat.le_findGreatest (P := P) hBoundK hPK
    have hCardLe : Fintype.card ↥K ≤ Fintype.card ↥M := by
      simpa [hMcard] using hLeN
    -- Step 3.4: The inclusion `M ≤ K` gives the reverse inequality on cardinalities.
    have hInj :
        Function.Injective (fun x : M => (⟨x, hMK x.property⟩ : K)) := by
      intro x y hxy
      ext
      simpa using congrArg Subtype.val hxy
    have hCardLe' : Fintype.card ↥M ≤ Fintype.card ↥K :=
      Fintype.card_le_of_injective _ hInj
    have hCardEq : Fintype.card ↥M = Fintype.card ↥K :=
      le_antisymm hCardLe' hCardLe
    -- Step 3.5.1: Compare the cardinality–index identities for `M` and `K`.
    have hMindex :
        Fintype.card ↥M * M.index = Fintype.card G := by
      simpa [Nat.card_eq_fintype_card] using M.card_mul_index
    have hKindex :
        Fintype.card ↥K * K.index = Fintype.card G := by
      simpa [Nat.card_eq_fintype_card] using K.card_mul_index
    have hIndexEqRaw :
        Fintype.card ↥M * M.index = Fintype.card ↥M * K.index := by
      simpa [hCardEq] using hMindex.trans hKindex.symm
    -- Step 3.5.2: Cancel the positive cardinality factor to conclude `M.index = K.index`.
    have hMpos : 0 < Fintype.card ↥M :=
      Fintype.card_pos_iff.mpr ⟨⟨1, M.one_mem⟩⟩
    have hIndexEq : M.index = K.index :=
      Nat.eq_of_mul_eq_mul_left hMpos hIndexEqRaw
    -- Step 3.5.3: Plug the index equality into the relative index formula.
    have hRelEq :
        M.relIndex K * K.index = K.index := by
      simpa [hIndexEq] using Subgroup.relIndex_mul_index (H := M) (K := K) hMK
    have hIndexNeZero : K.index ≠ 0 := by
      classical
      simpa using (K.index_ne_zero_of_finite : K.index ≠ 0)
    have hRelEq' : K.index * M.relIndex K = K.index * 1 := by
      have : K.index * M.relIndex K = K.index := by
        simpa [Nat.mul_comm] using hRelEq
      simpa [Nat.mul_one] using this
    have hRelIndex : M.relIndex K = 1 :=
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hIndexNeZero) hRelEq'
    -- Step 3.5.4: Relative index `1` means `K ≤ M`, hence `K = M`.
    have hKleM : K ≤ M :=
      (Subgroup.relIndex_eq_one (H := M) (K := K)).1 hRelIndex
    exact Or.inl (le_antisymm hKleM hMK)
