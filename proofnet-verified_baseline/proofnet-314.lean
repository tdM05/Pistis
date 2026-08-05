import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Show that if $\prod X_\alpha$ is Hausdorff, then so is $X_\alpha$. Assume that each $X_\alpha$ is nonempty.
-/

/-Informal Proof

Suppose that $X=\prod_\beta X_\beta$ is Hausdorff and let $\alpha$ be any index.
Let $x, y \in X_\alpha$ be any points such that $x \neq y$. Since all $X_\beta$ are nonempty, there exist points $\mathbf{x}, \mathbf{y} \in X$ such that $x_\beta=y_\beta$ for every $\beta \neq \alpha$ and $x_\alpha=x, y_\alpha=y$.
Since $x \neq y$, it follows that $\mathbf{x} \neq \mathbf{y}$. Since $X$ is Hausdorff, there exist open disjoint sets $U, V \subseteq X$ such that $\mathbf{x} \in U$ and $\mathbf{y} \in V$.
For $\beta \neq \alpha$ we have that $x_\beta=y_\beta \in \pi_\beta(U) \cap \pi_\beta(V)$, hence $\pi_\beta(U)$ and $\pi_\beta(V)$ are not disjoint.
Since $U$ and $V$ are disjoint, it follows that $\pi_\alpha(U) \cap \pi_\alpha(V)=\emptyset$.
We also have that $x \in \pi_\alpha(U)$ and $y \in \pi_\alpha(V)$ and since the projections are open maps, it follows that the sets $\pi_\alpha(U)$ and $\pi_\alpha(V)$ are open.
This proves that $x$ and $y$ can be separated by open sets, so $X_\alpha$ is Hausdorff.
-/

theorem Munkres_exercise_32_2a
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : T2Space (Π i, X i)) :
  ∀ i, T2Space (X i) := by
  -- Step 0: Switch to classical logic so that we can freely use choice and decidable equality.
  classical
  -- Step 1: Fix an index `i` and choose a reference point in each coordinate using `h`.
  intro i
  let base : (Π j, X j) := fun j => Classical.choice (h j)
  -- Step 2: Embed `X i` into the product by updating the reference function at coordinate `i`.
  let σ : X i → Π j, X j := fun z => Function.update base i z
  -- Step 2.1: Record that this embedding is continuous (constant map updated in one coordinate).
  have hσ : Continuous σ := by
    simpa [σ, base] using (continuous_const : Continuous fun _ : X i => base).update i
      (continuous_id : Continuous fun z : X i => z)
  -- Step 3: Prove the Hausdorff (pairwise separation) property for `X i`.
  refine ⟨?_⟩
  intro x y hxy
  -- Step 3.1: View `x` and `y` as points inside the product via `σ`.
  have hσxy : σ x ≠ σ y := by
    -- Step 3.2: Evaluate both sides at coordinate `i` to turn equality in the product into equality in `X i`.
    intro hxyProd
    have : (σ x) i = (σ y) i := congrArg (fun f => f i) hxyProd
    -- Step 3.2.1: Evaluating the updates shows that we would get `x = y`, contradicting `hxy`.
    have : x = y := by
      simpa [σ] using this
    exact hxy this
  -- Step 3.3: Apply the Hausdorff property of the product to separate `σ x` and `σ y`.
  obtain ⟨U, V, hUopen, hVopen, hxU, hyV, hUVdisj⟩ :=
    t2_separation (x := σ x) (y := σ y) hσxy
  -- Step 3.4: Pull the separating neighborhoods back through `σ` to get neighborhoods in `X i`.
  refine ⟨σ ⁻¹' U, σ ⁻¹' V, ?_, ?_, ?_, ?_, ?_⟩
  -- Step 3.4.1: Continuity of `σ` sends open sets to open preimages.
  · exact hUopen.preimage hσ
  · exact hVopen.preimage hσ
  -- Step 3.4.2: Membership of `σ x` and `σ y` transfers to the preimages.
  · simpa [Set.preimage, σ] using hxU
  · simpa [Set.preimage, σ] using hyV
  -- Step 3.4.3: Preimages of disjoint sets remain disjoint.
  · refine Set.disjoint_left.mpr ?_
    intro z hzU hzV
    -- Step 3.4.4: If a point pulls back into both sets, its image would lie in both `U` and `V`,
    -- contradicting the disjointness we got from the Hausdorff property of the product.
    change σ z ∈ U at hzU
    change σ z ∈ V at hzV
    exact Set.disjoint_left.mp hUVdisj hzU hzV
