import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Prove that no group of order 224 is simple.
-/

/-Informal Proof

The following proves there must exist a normal Sylow 2 -subgroup of order 32 ,
Suppose there are $n_2=7$ Sylow 2 -subgroups in $G$. Making $G$ act on the set of these Sylow subgroups by conjugation (Mitt wrote about this but on the set of the other Sylow subgroups, which gives no contradiction), we get a homomorphism $G \rightarrow S_7$ which must be injective if $G$ is simple (why?).

But this cannot be since then we would embed $G$ into $S_7$, which is impossible since $|G| \nmid 7 !=\left|S_7\right|$ (why?)
-/

theorem Artin_exercise_6_4_12 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 224) :
  IsSimpleGroup G → false := by
  classical
  -- Step 1: turn the hypothesis `IsSimpleGroup G` into an instance so we can use lemmas conveniently.
  intro hSimple
  haveI := hSimple
  -- Step 2: fix a Sylow 2-subgroup `P` of `G` (exists by Sylow).
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := Classical.choice (inferInstance : Nonempty (Sylow 2 G))
  -- Step 3: compute the exact order of `P` using the standard Sylow cardinality formula.
  --         The group order is 224 = 2^5 * 7, so the 2-Sylow has order 2^5 = 32.
  have hCardP : Fintype.card P = 32 := by
    -- Step 3.1: the abstract formula `|P| = 2 ^ v₂(|G|)`.
    have h := Sylow.card_eq_multiplicity (G := G) (p := 2) P
    -- Step 3.2: rewrite into `Fintype.card`.
    have h' : Fintype.card P = 2 ^ Nat.factorization (Fintype.card G) 2 := by
      simpa [Nat.card_eq_fintype_card] using h
    -- Step 3.3: evaluate the factorization of 224 at 2: it is 5.
    have hFactor : Nat.factorization (Fintype.card G) 2 = 5 := by
      have : Nat.factorization 224 2 = 5 := by native_decide
      simpa [hG] using this
    -- Step 3.4: finish the numeric simplification.
    norm_num [h', hFactor]
  -- Step 4: compute the index of `P` in `G`, which is |G| / |P| = 224 / 32 = 7 (a prime).
  have hIndex : P.index = 7 := by
    -- Step 4.1: use the identity |P| * [G:P] = |G| and solve the resulting equation.
    have hMul : P.index * Fintype.card P = Fintype.card G := by
      have h := (P : Subgroup G).index_mul_card
      -- turn all `Nat.card` into `Fintype.card` for easier numeric rewrites
      simpa [Nat.card_eq_fintype_card] using h
    have hEq : (32 : ℕ) * P.index = 224 := by
      have h := hMul
      -- rewrite both cardinalities to concrete numbers
      simp [hG, hCardP] at h
      -- reorder to match the desired form
      simpa [mul_comm] using h
    -- Step 4.2: solve the linear equation in ℤ to avoid nat-division hassles.
    have hEqZ : (32 : ℤ) * (P.index : ℤ) = 224 := by exact_mod_cast hEq
    have hIndexZ : (P.index : ℤ) = 7 := by nlinarith
    exact_mod_cast hIndexZ
  -- Step 5: show the normal core of `P` is trivial (⊥), forced by simplicity plus `P` being proper.
  have hCoreBot : P.normalCore = (⊥ : Subgroup G) := by
    -- Step 5.1: simplicity says any normal subgroup is ⊥ or ⊤.
    have hCoreNormal : (P.normalCore).Normal := Subgroup.normalCore_normal (H := (P : Subgroup G))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := P.normalCore) hCoreNormal with hCore | hCore
    · -- Step 5.2: if it is ⊥ we are done.
      exact hCore
    · -- Step 5.3: exclude the ⊤ possibility using the already computed index.
      have hTopLeP : (⊤ : Subgroup G) ≤ (P : Subgroup G) := by
        have hLe : P.normalCore ≤ (P : Subgroup G) := Subgroup.normalCore_le (H := (P : Subgroup G))
        rw [hCore] at hLe
        exact hLe
      have hPtop : (P : Subgroup G) = ⊤ := top_unique hTopLeP
      have hIndexOne : P.index = 1 := by
        -- index of ⊤ is 1
        simp [hPtop]
      -- contradiction because we already proved the index is 7
      simp [hIndexOne] at hIndex
  -- Step 6: use the action of `G` on the cosets of `P`.  The kernel is the normal core,
  --         so the core index divides the factorial of the coset count.
  have hCoreFactorial : P.normalCore.index ∣ Nat.factorial P.index := by
    -- Step 6.1: identify the kernel with the normal core.
    have hKer :
        P.normalCore = (MulAction.toPermHom G (G ⧸ (P : Subgroup G))).ker := by
      simp [Subgroup.normalCore_eq_ker (H := (P : Subgroup G))]
    -- Step 6.2: relate the index of the kernel to the size of the image.
    have hIndexKer :
        P.normalCore.index =
          Nat.card (MulAction.toPermHom G (G ⧸ (P : Subgroup G))).range := by
      simpa [hKer] using
        (index_ker (MulAction.toPermHom G (G ⧸ (P : Subgroup G))))
    -- Step 6.3: the image sits inside the full symmetric group.
    have hRangeDiv :
        Nat.card (MulAction.toPermHom G (G ⧸ (P : Subgroup G))).range ∣
          Nat.card (Equiv.Perm (G ⧸ (P : Subgroup G))) :=
      card_subgroup_dvd_card _
    -- Step 6.4: rewrite the divisibility using the identifications above.
    have hDiv1 :
        P.normalCore.index ∣ Nat.card (Equiv.Perm (G ⧸ (P : Subgroup G))) := by
      simpa [hIndexKer] using hRangeDiv
    have hPermCardNat :
        Nat.card (Equiv.Perm (G ⧸ (P : Subgroup G))) =
          Nat.factorial (Nat.card (G ⧸ (P : Subgroup G))) :=
      Nat.card_perm (α := G ⧸ (P : Subgroup G))
    have hDiv2 :
        P.normalCore.index ∣ Nat.factorial (Nat.card (G ⧸ (P : Subgroup G))) := by
      exact hPermCardNat ▸ hDiv1
    -- Step 6.5: replace the coset count with the subgroup index.
    have hIndexCardNat : Nat.card (G ⧸ (P : Subgroup G)) = P.index :=
      (Subgroup.index_eq_card (H := (P : Subgroup G))).symm
    have hDiv3 : P.normalCore.index ∣ Nat.factorial P.index := by
      exact hIndexCardNat ▸ hDiv2
    exact hDiv3
  -- Step 7: substitute `normalCore = ⊥` and `P.index = 7` to get `|G| ∣ 7! = 5040`.
  have hCardDiv : Fintype.card G ∣ 5040 := by
    -- rewrite the left using the core being ⊥ (index of ⊥ is |G|) and the right using the computed index.
    have hCoreIndex : P.normalCore.index = Fintype.card G := by
      simp [hCoreBot, Nat.card_eq_fintype_card]
    have hIndexFactorial : Nat.factorial P.index = 5040 := by norm_num [hIndex]
    have h' : Fintype.card G ∣ Nat.factorial P.index := by simpa [hCoreIndex] using hCoreFactorial
    simpa [hIndexFactorial] using h'
  -- Step 8: but numerically 224 ∤ 5040, contradiction; therefore no simple group of order 224 exists.
  simp [hG] at hCardDiv
