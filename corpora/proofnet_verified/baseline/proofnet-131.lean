import Mathlib

open Filter Set TopologicalSpace Topology
open scoped Topology


namespace Proofnet131

variable {ι : Type*} {X : ι → Type*} [∀ k, TopologicalSpace (X k)]
variable (h : ∀ i, Nonempty (X i))

noncomputable def baseChoice : Π i, X i :=
  fun i => Classical.choice (h i)

noncomputable def coordSection (i : ι) : X i → Π j, X j :=
  by
    classical
    refine fun y j =>
      if hji : j = i then by
        cases hji
        simpa
      else
        baseChoice h j

def sliceSet (i : ι) : Set (Π j, X j) :=
  {f | ∀ j ≠ i, f j = baseChoice h j}

omit [∀ k, TopologicalSpace (X k)] in
lemma coordSection_mem_slice (i : ι) (y : X i) :
    coordSection h i y ∈ sliceSet h i := by
  classical
  intro j hj
  dsimp [coordSection, sliceSet]
  simp [hj]

omit [∀ k, TopologicalSpace (X k)] in
lemma coordSection_self (i : ι) (y : X i) : coordSection h i y i = y := by
  classical
  dsimp [coordSection]
  simp

omit [∀ k, TopologicalSpace (X k)] in
lemma coordSection_ne (i : ι) (y : X i) {j : ι} (hj : j ≠ i) :
    coordSection h i y j = baseChoice h j := by
  classical
  dsimp [coordSection]
  simp [hj]

lemma coordSection_continuous (i : ι) : Continuous (coordSection h i) := by
  classical
  refine continuous_pi fun j => ?_
  by_cases hji : j = i
  · cases hji
    simpa [coordSection] using (continuous_id : Continuous (fun y : X i => y))
  · have : (fun y : X i => coordSection h i y j) = fun _ => baseChoice h j := by
      funext y
      exact coordSection_ne (h := h) i y hji
    simpa [this] using (continuous_const : Continuous fun _ : X i => baseChoice h j)

noncomputable def coordMap (i : ι) : X i → {f : Π j, X j // f ∈ sliceSet h i} :=
  fun y => ⟨coordSection h i y, coordSection_mem_slice (h := h) i y⟩

noncomputable def coordProj (i : ι) : {f : Π j, X j // f ∈ sliceSet h i} → X i :=
  fun f => f.1 i

lemma coordMap_continuous (i : ι) : Continuous (coordMap h i) := by
  classical
  exact
    (coordSection_continuous (h := h) i).subtype_mk
      (coordSection_mem_slice (h := h) i)

lemma coordProj_continuous (i : ι) : Continuous (coordProj (h := h) i) := by
  classical
  have : Continuous fun f : (Π j, X j) => f i := continuous_apply i
  exact this.comp continuous_subtype_val

omit [∀ k, TopologicalSpace (X k)] in
lemma coord_left_inv (i : ι) :
    Function.LeftInverse (coordProj (h := h) i) (coordMap (h := h) i) := by
  classical
  intro y
  dsimp [coordProj, coordMap]
  exact coordSection_self (h := h) i y

omit [∀ k, TopologicalSpace (X k)] in
lemma coord_right_inv (i : ι) :
    Function.RightInverse (coordProj (h := h) i) (coordMap (h := h) i) := by
  classical
  intro f
  ext j
  dsimp [coordProj, coordMap, coordSection]
  by_cases hji : j = i
  · subst hji
    simp
  · have hf : f.1 j = baseChoice h j := f.2 j hji
    simp [hji, hf]

noncomputable def coordHomeo (i : ι) :
    X i ≃ₜ {f : Π j, X j // f ∈ sliceSet h i} :=
  { toEquiv :=
      { toFun := coordMap (h := h) i
        invFun := coordProj (h := h) i
        left_inv := coord_left_inv (h := h) i
        right_inv := coord_right_inv (h := h) i }
    continuous_toFun := coordMap_continuous (h := h) i
    continuous_invFun := coordProj_continuous (h := h) i }

end Proofnet131

open Proofnet131


/-Informal Statement

Show that if $\prod X_\alpha$ is regular (separation property only), then so is $X_\alpha$. Assume that each $X_\alpha$ is nonempty.
-/

/-Informal Proof

Suppose that $X=\prod_\beta X_\beta$ is regular and let $\alpha$ be any index.
We have to prove that $X_\alpha$ satisfies the $T_1$ and the $T_3$ axiom.
Since $X$ is regular, it follows that $X$ is Hausdorff, which then implies that $X_\alpha$ is Hausdorff. However, this implies that $X_\alpha$ satisfies the $T_1$ axiom.

Let now $F \subseteq X_\alpha$ be a closed set and $x \in X_\alpha \backslash F$ a point.
Then $\prod_\beta F_\beta$, where $F_\alpha=F$ and $F_\beta=X_\beta$ for $\beta \neq \alpha$, is a closed set in $X$ since $\left(\prod_\beta F_\beta\right)^c=\prod_\beta U_\beta$, where $U_\alpha=F^c$ and $U_\beta=X_\beta$ for $\beta \neq \alpha$, which is an open set because it is a base element for the product topology.
Since all $X_\beta$ are nonempty, there exists a point $\mathbf{x} \in X$ such that $x_\alpha=x$. Then $\mathbf{x} \notin \prod_\beta F_\beta$.
Now since $X$ is regular (and therefore satisfies the $T_3$ axiom), there exist disjoint open sets $U, V \subseteq X$ such that $\mathbf{x} \in U$ and $\prod_\beta F_\beta \subseteq V$.

Now for every $\beta \neq \alpha$ we have that $x_\beta \in X_\beta=\pi_\beta(V)$. However, since $x_\beta \in \pi_\beta(U)$, it follows that $\pi_\beta(U) \cap \pi_\beta(V) \neq \emptyset$.
Then $U \cap V=\emptyset$ implies that $\pi_\alpha(U) \cap \pi_\alpha(V)=\emptyset$.. Also, $x \in \pi_\alpha(U)$ and $F \subseteq \pi_\alpha(V)$ and $\pi_\alpha(U), \pi_\alpha(V)$ are open sets since $\pi_\alpha$ is an open map.
Therefore, $X_\alpha$ satisfies the $T_3$ axiom.
-/

theorem Munkres_exercise_32_2b
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : RegularSpace (Π i, X i)) :
  ∀ i, RegularSpace (X i) := by
  classical
  -- Step 0: Upgrade the given regularity assumption on the product to a typeclass instance.
  haveI : RegularSpace (Π j, X j) := h2
  -- Step 1: Fix an arbitrary index and relate `X i` to the slice of the product where all
  --         other coordinates stay at their chosen base points.
  refine fun i => ?_
  -- Step 1.1: Use `coordHomeo` to view `X i` as homeomorphic to the subtype `sliceSet h i`.
  have hHomeo : Topology.IsInducing (coordHomeo (h := h) i) :=
    (coordHomeo (h := h) i).isInducing
  -- Step 1.2: Note that the subtype `sliceSet h i` is regular because it is a subspace of the
  --           regular product (no extra work needed thanks to the global instance).
  -- Step 2: Transfer regularity across the inducing homeomorphism.
  exact hHomeo.regularSpace
