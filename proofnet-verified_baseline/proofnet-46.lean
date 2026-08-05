import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $H$ is a nontrivial normal subgroup of the solvable group $G$ then there is a nontrivial subgroup $A$ of $H$ with $A \unlhd G$ and $A$ abelian.
-/

/-Informal Proof

Suppose $H$ is a nontrivial normal subgroup of the solvable group $G$.
First, notice that $H$, being a subgroup of a solvable group, is itself solvable. By exercise $8, H$ has a chain of subgroups
$$
1 \leq H_1 \leq \ldots \leq H
$$
such that each $H_i$ is a normal subgroup of $H$ itself and $H_{i+1} / H_i$ is abelian. But then the first group in the series
$$
H_1 / 1 \cong H
$$
is an abelian subgroup of $H$.
-/

theorem Dummit_Foote_exercise_3_4_11 {G : Type*} [Group G] [IsSolvable G]
  {H : Subgroup G} (hH : H ≠ ⊥) [H.Normal] :
  ∃ A ≤ H, A ≠ ⊥ ∧ A.Normal ∧ ∀ a b : A, a*b = b*a := by
  classical
  -- Step 1: Extract the solvability data for `H` and record the minimal derived-series index that collapses.
  -- Step 1.1: View the subgroup `H` as solvable because it sits inside the solvable group `G`.
  have hSolvInst : IsSolvable H := inferInstance
  -- Step 1.2: Choose the smallest `m` with `derivedSeries H m = ⊥` using `Nat.find`.
  have hSolv : ∃ n, derivedSeries (G := H) n = ⊥ := hSolvInst.solvable
  set m := Nat.find hSolv with hmdef
  -- Step 1.3: Record the defining property of `m`.
  have hm : derivedSeries (G := H) m = ⊥ := by
    simpa [hmdef] using Nat.find_spec hSolv
  -- Step 2: Show that `m` is positive by proving the zeroth derived term is nontrivial.
  -- Step 2.1: Because `H ≠ ⊥`, conclude that `H` is a nontrivial group.
  have hNontrivialH : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hH
  haveI := hNontrivialH
  -- Step 2.2: Pick an explicit element witnessing the nontriviality of `H`.
  obtain ⟨x, hx⟩ := exists_ne (1 : H)
  -- Step 2.3: Note that this element lies in the zeroth derived term but not in the trivial subgroup.
  have hx_top : x ∈ derivedSeries (G := H) 0 := by
    simp [derivedSeries_zero]
  have hx_not_bot : x ∉ (⊥ : Subgroup H) := by
    simp [Subgroup.mem_bot, hx]
  -- Step 2.4: Convert the two membership statements into the desired inequality.
  have hzero : derivedSeries (G := H) 0 ≠ (⊥ : Subgroup H) := by
    intro hEq
    have hx_bot : x ∈ (⊥ : Subgroup H) := by simpa [hEq] using hx_top
    exact hx_not_bot hx_bot
  -- Step 2.5: Deduce that `m` is strictly positive via the characterization of `Nat.find`.
  have hm_pos : 0 < m := by
    have hm_pos' : 0 < Nat.find hSolv := (Nat.find_pos hSolv).2 hzero
    exact hmdef.symm ▸ hm_pos'
  -- Step 3: Keep track of every derived term before `m`, which must stay nontrivial by minimality.
  -- Step 3.1: Translate the minimality of `m` into a reusable lemma.
  have hnontrivial_levels :
      ∀ l < m, derivedSeries (G := H) l ≠ (⊥ : Subgroup H) := by
    intro l hl hEq
    have hle : m ≤ l := by
      have := Nat.find_min' hSolv hEq
      simpa [hmdef] using this
    exact (not_le_of_gt hl) hle
  -- Step 4: Focus on the predecessor index `n` with `m = n + 1` and isolate the last nontrivial derived subgroup.
  -- Step 4.1: Rewrite `m` as a successor to access the previous derived term cleanly.
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm_pos)
  -- Step 4.2: Introduce `K = derivedSeries H n`, the final nontrivial term before the collapse.
  set K : Subgroup H := derivedSeries (G := H) n with hKdef
  -- Step 4.3: Establish that `K` is nontrivial thanks to the minimality of `m`.
  have hn_lt : n < m := Nat.lt_of_lt_of_eq (Nat.lt_succ_self n) hn.symm
  have hK_ne_bot : K ≠ (⊥ : Subgroup H) := by
    have := hnontrivial_levels n hn_lt
    simpa [hKdef] using this
  -- Step 5: Promote `K` to a subgroup `A` of `G` and verify the requested structural properties.
  -- Step 5.1: Map `K` back into `G` via the inclusion `H → G`.
  set A : Subgroup G := K.map H.subtype with hAdef
  -- Step 5.2: The image of `K` under the inclusion sits inside `H`.
  have hA_le : A ≤ H := by
    simpa [hAdef] using Subgroup.map_subtype_le (H := H) (K := K)
  -- Step 5.3: The subgroup `A` is nontrivial since `K` is nontrivial and the map is injective.
  have hA_ne_bot : A ≠ (⊥ : Subgroup G) := by
    intro hA
    refine hK_ne_bot ?_
    exact
      (Subgroup.map_eq_bot_iff_of_injective (H := K) (f := H.subtype) H.subtype_injective).1
        (by simpa [hAdef, hA])
  -- Step 5.4: Recognize that `A` is normal in `G` because `K` is characteristic in `H` and `H` is normal in `G`.
  have hA_normal : A.Normal := inferInstance
  -- Step 6: Prove that `A` is abelian, i.e., its elements mutually commute.
  -- Step 6.1: Identify the commutator of `K` with itself using the description of the derived series.
  have hCommK : ⁅K, K⁆ = (⊥ : Subgroup H) := by
    have hm_succ : derivedSeries (G := H) (n + 1) = ⊥ := by
      simpa [hn] using hm
    calc
      ⁅K, K⁆ = ⁅derivedSeries (G := H) n, derivedSeries (G := H) n⁆ := by
        simp [hKdef]
      _ = derivedSeries (G := H) (n + 1) :=
        (derivedSeries_succ (G := H) n).symm
      _ = (⊥ : Subgroup H) := hm_succ
  -- Step 6.2: Transport the zero commutator via the inclusion to obtain the commutator of `A`.
  have hCommA : ⁅A, A⁆ = (⊥ : Subgroup G) := by
    have hmap :
        (⁅K, K⁆).map H.subtype = (⊥ : Subgroup G) := by
      simpa [Subgroup.map_bot] using
        congrArg (fun S : Subgroup H => S.map H.subtype) hCommK
    have hmapcomm :
        (⁅K, K⁆).map H.subtype = ⁅A, A⁆ := by
      simpa [hAdef] using
        (Subgroup.map_commutator (H₁ := K) (H₂ := K) H.subtype)
    exact hmapcomm.symm.trans hmap
  -- Step 6.3: Translate the trivial commutator into a pointwise commutativity statement.
  have hA_comm : ∀ a b : A, a * b = b * a := by
    intro a b
    have hmem : ⁅(a : G), (b : G)⁆ ∈ ⁅A, A⁆ :=
      Subgroup.commutator_mem_commutator a.2 b.2
    have hmem_bot : ⁅(a : G), (b : G)⁆ ∈ (⊥ : Subgroup G) := by
      simpa [hCommA] using hmem
    have hcommEl : ⁅(a : G), (b : G)⁆ = (1 : G) := by
      simpa [Subgroup.mem_bot] using hmem_bot
    have hcommute : (a : G) * (b : G) = (b : G) * (a : G) :=
      (commutatorElement_eq_one_iff_mul_comm (g₁ := (a : G)) (g₂ := (b : G))).1 hcommEl
    refine Subtype.ext ?_
    simpa using hcommute
  -- Step 7: Assemble all properties to produce the desired subgroup `A`.
  exact ⟨A, hA_le, hA_ne_bot, hA_normal, hA_comm⟩
