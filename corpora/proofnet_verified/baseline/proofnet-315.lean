import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Show that if $\prod X_\alpha$ is normal, then so is $X_\alpha$. Assume that each $X_\alpha$ is nonempty.
-/

/-Informal Proof

Suppose that $X=\prod_\beta X_\beta$ is normal and let $\alpha$ be any index.
Since $X$ is normal, it follows that $X$ is Hausdorff (or regular), which then implies that $X_\alpha$ is Hausdorff (or regular). This imples that $X_\alpha$ satisfies the $T_1$ axiom.
Now the proof that $X_\alpha$ satisfies the $T_4$ axiom is the same as for regular spaces.
If $F, G \subseteq X_\alpha$ are disjoint closed sets, then $\prod_\beta F_\beta$ and $\prod_\beta G_\beta$, where $F_\alpha=F, G_\alpha=G$ and $F_\beta=G_\beta=X_\beta$ for $\beta \neq \alpha$, are disjoint closed sets in $X$.
Since $X$ is normal (and therefore satisfies the $T_4$ axiom), there exist disjoint open sets $U, V \subseteq X$ such that $\prod_\beta F_\beta \subseteq U$ and $\prod_\beta G_\beta \subseteq V$
Then $\pi_\alpha(U)$ and $\pi_\alpha(V)$ are disjoint open sets in $X_\alpha$ such that $F \subseteq \pi_\alpha(U)$ and $G \subseteq \pi_\alpha(V)$.
-/

theorem Munkres_exercise_32_2c
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  classical
  haveI := h2
  -- Step 1: Fix a canonical element in each coordinate using the nonemptiness hypothesis.
  let base : Π j, X j := fun j => Classical.choice (h j)
  intro i
  -- Step 2: Provide the normality structure for the `i`-th coordinate.
  refine
    { normal := ?_ }
  intro F G hF hG hdis
  -- Step 2.1: Lift the closed sets to the product via the projection onto the `i`-th coordinate.
  let proj : (Π j, X j) → X i := fun x => x i
  have hproj : Continuous proj := continuous_apply i
  let s : Set (Π j, X j) := proj ⁻¹' F
  let t : Set (Π j, X j) := proj ⁻¹' G
  -- Step 2.2: The lifted sets remain closed thanks to continuity of the projection.
  have hs : IsClosed s := hF.preimage hproj
  have ht : IsClosed t := hG.preimage hproj
  -- Step 2.3: Disjointness also lifts because different fibers would project to a common point.
  have hdis' : Disjoint s t := by
    refine Set.disjoint_left.2 ?_
    intro x hx hx'
    exact Set.disjoint_left.1 hdis hx hx'
  -- Step 3: Separate the lifted sets using the normality of the whole product.
  have hsep : SeparatedNhds s t := normal_separation hs ht hdis'
  -- Step 4: Build a continuous section selecting the `i`-th coordinate while freezing others.
  let φ : X i → Π j, X j := fun x => Function.update base i x
  have hφ : Continuous φ := by
    -- Step 4.1: View the section as a composition of a constant-identity pair with `continuous_update`.
    have hpair :
        Continuous fun x : X i => (base, x) :=
      (continuous_const : Continuous fun _ : X i => base).prodMk
        (continuous_id : Continuous fun x : X i => x)
    have hupdate :
        Continuous fun f : (Π j, X j) × X i => Function.update f.1 i f.2 :=
      continuous_update (A := fun j => X j) i
    simpa [φ] using hupdate.comp hpair
  -- Step 5: Pull back the separated neighbourhoods along the section and identify the fibers.
  have hpre_s : φ ⁻¹' s = F := by
    ext x; simp [s, proj, φ]
  have hpre_t : φ ⁻¹' t = G := by
    ext x; simp [t, proj, φ]
  -- Step 5.1: The pulled-back separation gives the desired separation on `F` and `G`.
  simpa [hpre_s, hpre_t] using hsep.preimage hφ
