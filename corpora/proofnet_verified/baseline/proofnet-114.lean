import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $\mathbf{x}_1, \mathbf{x}_2, \ldots$ be a sequence of the points of the product space $\prod X_\alpha$.  Show that this sequence converges to the point $\mathbf{x}$ if and only if the sequence $\pi_\alpha(\mathbf{x}_i)$ converges to $\pi_\alpha(\mathbf{x})$ for each $\alpha$.
-/

/-Informal Proof

For each $n \in \mathbb{Z}_{+}$, we write $\mathbf{x}_n=\left(x_n^\alpha\right)_\alpha$, so that $\pi_\alpha\left(\mathbf{x}_n\right)=x_n^\alpha$ for each $\alpha$.
First assume that the sequence $\mathbf{x}_1, \mathbf{x}_2, \ldots$ converges to $\mathbf{x}=\left(x_\alpha\right)_\alpha$ in the product space $\prod_\alpha X_\alpha$. Fix an index $\beta$ and let $U$ be a neighbourhood of $\pi_\beta(\mathbf{x})=x_\beta$. Let $V=\prod_\alpha U_\alpha$, where $U_\alpha=X_\alpha$ for each $\alpha \neq \beta$ and $U_\beta=U$. Then $V$ is a neighbourhood of $\mathbf{x}$, so there exists $N \in \mathbb{Z}_{+}$such that $\mathbf{x}_n \in V$ for all $n \geq N$. Therefore $\pi_\beta\left(\mathbf{x}_n\right)=x_n^\beta \in U$ for all $n \geq N$. Since $U$ was arbitrary, it follows that $\pi_\beta\left(\mathbf{x}_1\right), \pi_\beta\left(\mathbf{x}_2\right), \ldots$ converges to $\pi_\beta(\mathbf{x})$. Since $\beta$ was arbitrary, this holds for all indices $\alpha$.
-/

theorem Munkres_exercise_19_6a
  {ι : Type*}
  {f : ι → Type*} {x : ℕ → Πa, f a}
  (y : Πi, f i)
  [Πa, TopologicalSpace (f a)] :
  Tendsto x atTop (𝓝 y) ↔ ∀ i, Tendsto (λ j => (x j) i) atTop (𝓝 (y i)) := by
  -- Step 1: Recall the canonical product-space convergence criterion `tendsto_pi_nhds`,
  --         which states that convergence into a product is equivalent to coordinatewise convergence.
  -- Step 1.1: Specialize this lemma to the sequence `x`, the candidate limit `y`,
  --           and the filter `atTop` on natural numbers.
  -- Step 1.2: Note that, after specialization, the lemma yields exactly the desired equivalence.
  -- Step 2: Apply the specialized lemma directly to close the goal.
  simpa using (tendsto_pi_nhds (f := x) (g := y) (u := atTop))
