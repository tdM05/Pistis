import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Show that the subgroup of all rotations in a dihedral group is a maximal subgroup.
-/

/-Informal Proof

Fix a positive integer $n>1$ and let $H \leq D_{2 n}$ consist of the rotations of $D_{2 n}$. That is, $H=\langle r\rangle$. Now, this subgroup is proper since it does not contain $s$. If $H$ is not maximal, then by the previous proof we know there is a maximal subset $K$ containing $H$. Then $K$ must contain a reflection $s r^k$ for $k \in\{0,1, \ldots, n-1\}$. Then since $s r^k \in K$ and $r^{n-k} \in K$, it follows by closure that
$$
s=\left(s r^k\right)\left(r^{n-k}\right) \in K .
$$
But $D_{2 n}=\langle r, s\rangle$, so this shows that $K=D_{2 n}$, which is a contradiction. Therefore $H$ must be maximal.
-/

theorem Dummit_Foote_exercise_2_4_16b {n : ℕ} {hn : n ≠ 0}
  {R : Subgroup (DihedralGroup n)}
  (hR : R = Subgroup.closure {DihedralGroup.r 1}) :
  R ≠ ⊤ ∧
  ∀ K : Subgroup (DihedralGroup n), R ≤ K → K = R ∨ K = ⊤ := by
  classical
  -- Step 0: upgrade the hypothesis `hn` to a reusable type-class witness.
  haveI : NeZero n := ⟨hn⟩
  -- Step 1: recognise `R` as the subgroup of all integer powers of the basic rotation.
  -- Step 1.1: the standard lemma `zpowers_eq_closure` performs the identification.
  have hR_zpowers :
      Subgroup.zpowers (DihedralGroup.r (1 : ZMod n)) = R := by
    exact
      (Subgroup.zpowers_eq_closure (DihedralGroup.r (1 : ZMod n))).trans hR.symm
  -- Step 2: prove that every rotation necessarily lies inside `R`.
  -- Step 2.1: fix an arbitrary rotation index and pick an integer representative.
  have hr_mem : ∀ j : ZMod n, DihedralGroup.r j ∈ R := by
    intro j
    -- Step 2.2: use surjectivity of `ℤ → ZMod n` to choose an exponent producing `j`.
    obtain ⟨m, hm⟩ := (ZMod.intCast_surjective (n := n)) j
    -- Step 2.3: integer powers of `r 1` belong to the `zpowers` subgroup by construction.
    have hmem :
        (DihedralGroup.r (1 : ZMod n)) ^ m
          ∈ Subgroup.zpowers (DihedralGroup.r (1 : ZMod n)) :=
      Subgroup.zpow_mem_zpowers _ m
    -- Step 2.4: reinterpret the membership using the description from Step 1.
    have hmemR :
        (DihedralGroup.r (1 : ZMod n)) ^ m ∈ R := by
      simpa [hR_zpowers] using hmem
    -- Step 2.5: rewrite the power as the required rotation.
    simpa [DihedralGroup.r_one_zpow (n := n) (k := m), hm] using hmemR
  -- Step 3: establish that the fundamental reflection can never lie in `R`.
  have h_sr_not_mem :
      DihedralGroup.sr (0 : ZMod n) ∉ R := by
    -- Step 3.1: argue by contradiction, moving back to the `zpowers` viewpoint.
    intro hmem
    have hzpow :
        DihedralGroup.sr (0 : ZMod n)
          ∈ Subgroup.zpowers (DihedralGroup.r (1 : ZMod n)) := by
      simpa [hR_zpowers] using hmem
    -- Step 3.2: extract the corresponding exponent and translate into an equality.
    rcases Subgroup.mem_zpowers_iff.mp hzpow with ⟨m, hm⟩
    have hrot :
        DihedralGroup.r (m : ZMod n) = DihedralGroup.sr (0 : ZMod n) := by
      simp [DihedralGroup.r_one_zpow (n := n) (k := m)] at hm
    -- Step 3.3: exploit constructor disjointness to reach a contradiction.
    have hne :
        DihedralGroup.r (m : ZMod n) ≠ DihedralGroup.sr (0 : ZMod n) := by
      -- Step 3.3.1: `simp` with decidable equality distinguishes rotations from reflections.
      simp
    exact hne hrot
  -- Step 4: assemble the properness and maximality conclusions.
  refine ⟨?_, ?_⟩
  -- Step 4.1: if `R = ⊤`, the forbidden reflection would belong to `R`, contradiction.
  · intro htop
    have hmem :
        DihedralGroup.sr (0 : ZMod n) ∈ R := by
      simp [htop]
    exact h_sr_not_mem hmem
  -- Step 4.2: any subgroup strictly bigger than `R` must already equal the whole group.
  · intro K hRK
    by_cases hKR : K = R
    · -- Step 4.2.1: equality gives the first disjunct.
      exact Or.inl hKR
    · -- Step 4.2.2: otherwise extract an element of `K` that escapes `R`.
      have hnotle : ¬ K ≤ R := by
        intro hle
        exact hKR ((le_antisymm hRK hle).symm)
      -- Step 4.2.2.1: the negated inclusion yields a concrete counterexample.
      have hx_exists :
          ∃ x : DihedralGroup n, x ∈ K ∧ x ∉ R := by
        classical
        by_contra h
        apply hnotle
        intro x hxK
        by_contra hxR
        exact h ⟨x, hxK, hxR⟩
      obtain ⟨x, hxK, hxR⟩ := hx_exists
      -- Step 4.2.3: analyse whether the witness is a rotation or a reflection.
      cases' x with i i
      · -- Step 4.2.3.1: rotations always lie in `R`, contradiction.
        exact (hxR (hr_mem i)).elim
      · -- Step 4.2.3.2: a reflection forces `K` to absorb all reflections.
        -- Step 4.2.3.2.1: build the canonical reflection `sr 0` using the available rotation.
        have hsr0 :
            DihedralGroup.sr (0 : ZMod n) ∈ K := by
          have hrot_neg : DihedralGroup.r (-i) ∈ K := hRK (hr_mem (-i))
          have hmul :
              DihedralGroup.sr i * DihedralGroup.r (-i) ∈ K :=
            K.mul_mem hxK hrot_neg
          simpa [DihedralGroup.sr_mul_r] using hmul
        -- Step 4.2.3.2.2: thereafter every reflection enters via `sr 0 * r j`.
        have h_ref_mem : ∀ j : ZMod n, DihedralGroup.sr j ∈ K := by
          intro j
          have hmul :
              DihedralGroup.sr (0 : ZMod n) * DihedralGroup.r j ∈ K :=
            K.mul_mem hsr0 (hRK (hr_mem j))
          simpa [DihedralGroup.sr_mul_r] using hmul
        -- Step 4.2.3.2.3: confirm that every element of the dihedral group lies in `K`.
        have htop_le : ⊤ ≤ K := by
          intro g _
          cases' g with j j
          · -- Step 4.2.3.2.3.1: rotations are already in `K`.
            exact hRK (hr_mem j)
          · -- Step 4.2.3.2.3.2: reflections are handled by the previous sub-step.
            exact h_ref_mem j
        -- Step 4.2.3.2.4: thus `K` must coincide with the whole group.
        exact Or.inr (le_antisymm le_top htop_le)
