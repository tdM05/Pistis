import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $A \subset X$; let $f: A \rightarrow Y$ be continuous; let $Y$ be Hausdorff. Show that if $f$ may be extended to a continuous function $g: \bar{A} \rightarrow Y$, then $g$ is uniquely determined by $f$.
-/

/-Informal Proof

Let $h, g: \bar{A} \rightarrow Y$ be continuous extensions of $f$. Suppose that there is a point $x \in \bar{A}$ such that $h(x) \neq g(x)$. Since $h=g$ on $A$, we must have $x \in A^{\prime}$. Since $Y$ is Hausdorff, there is a neighbourhood $U$ of $h(x)$ and a neighbourhood $V$ of $g(x)$ such that $U \cap V=\emptyset$. Since $h$ and $g$ are continuous, $h^{-1}(U) \cap g^{-1}(V)$ is a neighbourhood of $x$. Since $x \in A^{\prime}$, there is a point $y \in h^{-1}(U) \cap g^{-1}(V) \cap A$ different from $x$. But $h=g$ on $A$, so $g^{-1}(V) \cap A=h^{-1}(V) \cap A$ and hence $y \in h^{-1}(U) \cap h^{-1}(V)=h^{-1}(U \cap V)=\emptyset$, a contradiction. It follows that $h=g$ on $\bar{A}$.
-/

theorem Munkres_exercise_18_13
  {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  {A : Set X} {f : X → Y} (hf : ContinuousOn f A)
  (g : X → Y) (g_con : ContinuousOn g (closure A))
  (gExt : ∀ x : A, g x = f x) :
  ∀ (g' : X → Y), (ContinuousOn g' (closure A) ∧ (∀ x : A, g' x = f x)) → (∀ x : closure A, g x = g' x) := by
  classical
  -- Step 0: Record the provided continuity of `f` on `A` so that every assumption from the statement is explicitly acknowledged.
  have _hf_record := hf
  -- Step 1: Introduce an arbitrary candidate extension `g'` together with its continuity and agreement data.
  intro g' hdata
  rcases hdata with ⟨hg'_con, hg'_agree⟩
  -- Step 2: Fix a point `x` in `closure A` and prove the equality by contradiction.
  intro x
  -- Step 2.1: Establish the desired equality `g x = g' x` by excluding the possibility that they differ.
  have hxEq : g x = g' x := by
    -- Step 2.1.1: Assume `g x ≠ g' x` and separate their images using the Hausdorff property of `Y`.
    classical
    by_contra hneq
    obtain ⟨U, V, hUopen, hVopen, hxU, hxV, hUVdisj⟩ := t2_separation hneq
    -- Step 2.1.2: Use continuity within `closure A` to pull the disjoint neighborhoods back to `x`.
    have hxU_pre :
        g ⁻¹' U ∈ nhdsWithin (x : X) (closure A) :=
      (g_con (x : X) x.property).preimage_mem_nhdsWithin (IsOpen.mem_nhds hUopen hxU)
    have hxV_pre :
        g' ⁻¹' V ∈ nhdsWithin (x : X) (closure A) :=
      (hg'_con (x : X) x.property).preimage_mem_nhdsWithin (IsOpen.mem_nhds hVopen hxV)
    -- Step 2.1.3: Intersect the pulled-back neighborhoods to obtain a common relative neighborhood of `x`.
    have hxS :
        (g ⁻¹' U ∩ g' ⁻¹' V) ∈ nhdsWithin (x : X) (closure A) :=
      inter_mem hxU_pre hxV_pre
    -- Step 2.1.4: Rewrite the membership in `nhdsWithin` so that we get an ordinary neighborhood `t` of `x`
    --            whose intersection with `closure A` lies inside the pulled-back sets.
    obtain ⟨t, ht_nhds, ht_subset⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hxS
    obtain ⟨o, ho_subset, ho_open, hx_mem_o⟩ := mem_nhds_iff.1 ht_nhds
    -- Step 2.1.5: Because `x ∈ closure A`, every open neighborhood of `x` meets `A`; find a witness `y ∈ A ∩ o`.
    have hA_nonempty :
        (o ∩ A).Nonempty :=
      (mem_closure_iff.1 x.property) o ho_open hx_mem_o
    obtain ⟨y, hy_in_o, hy_in_A⟩ := hA_nonempty
    -- Step 2.1.6: Record that `y` also lies in `t`, in `closure A`, and hence in the pulled-back intersection.
    have hy_in_t : y ∈ t := ho_subset hy_in_o
    have hy_in_closure : y ∈ closure A := subset_closure hy_in_A
    have hy_in_S :
        y ∈ g ⁻¹' U ∩ g' ⁻¹' V :=
      ht_subset ⟨hy_in_t, hy_in_closure⟩
    -- Step 2.1.7: Translate membership information back through the maps and exploit that `g` and `g'` agree with `f` on `A`.
    have hy_U : g y ∈ U := hy_in_S.1
    have hy_V : g' y ∈ V := hy_in_S.2
    have hy_eq : g y = g' y := by
      have hyg : g y = f y := gExt ⟨y, hy_in_A⟩
      have hyg' : g' y = f y := hg'_agree ⟨y, hy_in_A⟩
      exact hyg.trans hyg'.symm
    -- Step 2.1.8: Combine the previous step with the disjointness of `U` and `V` to obtain the contradiction.
    have hy_in_V' : g y ∈ V := by simpa [hy_eq] using hy_V
    have hy_empty : g y ∈ (∅ : Set Y) := hUVdisj.le_bot ⟨hy_U, hy_in_V'⟩
    exact hy_empty.elim
  -- Step 3: Conclude by returning the equality obtained via the contradiction argument.
  exact hxEq
