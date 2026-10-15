import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Suppose $\left\{p_{n}\right\}$ is a Cauchy sequence in a metric space $X$, and some subsequence $\left\{p_{n l}\right\}$ converges to a point $p \in X$. Prove that the full sequence $\left\{p_{n}\right\}$ converges to $p$.
-/

/-Informal Proof

Let $\varepsilon>0$. Choose $N_1$ so large that $d\left(p_m, p_n\right)<\frac{\varepsilon}{2}$ if $m>N_1$ and $n>N_1$. Then choose $N \geq N_1$ so large that $d\left(p_{n_k}, p\right)<\frac{\varepsilon}{2}$ if $k>N$. Then if $n>N$, we have
$$
d\left(p_n, p\right) \leq d\left(p_n, p_{n_{N+1}}\right)+d\left(p_{n_{N+1}}, p\right)<\varepsilon
$$
For the first term on the right is less than $\frac{\varepsilon}{2}$ since $n>N_1$ and $n_{N+1}>N+1>$ $N_1$. The second term is less than $\frac{\varepsilon}{2}$ by the choice of $N$.
-/

theorem Rudin_exercise_3_20 {X : Type*} [MetricSpace X]
  (p : ℕ → X) (l : ℕ+) (r : X)
  (hp : CauchySeq p)
  (hpl : Tendsto (λ n => p (l * n)) atTop (𝓝 r)) :
  Tendsto p atTop (𝓝 r) := by
  -- Step 1: Reduce the goal to the ε–criterion for convergence in a metric space.
  refine Metric.tendsto_nhds.mpr ?_
  -- Step 2: Fix an arbitrary ε > 0 that we must eventually satisfy.
  intro ε hε
  -- Step 2.1: Observe that ε / 2 is still positive, so it can be used for both bounds.
  have hεhalf : 0 < ε / 2 := half_pos hε
  -- Step 3: Apply the Cauchy property to obtain an index that makes the sequence self-close.
  obtain ⟨N₁, hN₁⟩ := (Metric.cauchySeq_iff.1 hp) (ε / 2) hεhalf
  -- Step 4: Exploit the convergence of the subsequence to get actual proximity to r.
  have hSub := (Metric.tendsto_nhds.1 hpl) (ε / 2) hεhalf
  -- Step 4.1: Extract an explicit rank after which the subsequence stays within ε / 2 of r.
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hSub
  -- Step 5: Choose a single subsequence index that simultaneously satisfies both constraints.
  let K : ℕ := max N₁ N₂
  -- Step 5.1: Record the elementary inequalities that K satisfies.
  have hK_ge_N₁ : N₁ ≤ K := le_max_left _ _
  have hK_ge_N₂ : N₂ ≤ K := le_max_right _ _
  -- Step 5.2: Show that the actual index l * K is also beyond the Cauchy threshold.
  have hOne_le : (1 : ℕ) ≤ (l : ℕ) := Nat.succ_le_of_lt l.pos
  have hK_le_lK : K ≤ (l : ℕ) * K := by
    simpa [one_mul] using (Nat.mul_le_mul_right K hOne_le)
  have hN₁_le_lK : N₁ ≤ (l : ℕ) * K := le_trans hK_ge_N₁ hK_le_lK
  -- Step 5.3: Record that the frozen subsequence element p (l * K) is ε / 2-close to r.
  have hSub_close : dist (p ((l : ℕ) * K)) r < ε / 2 := hN₂ K hK_ge_N₂
  -- Step 6: Turn all the previous data into a concrete eventual bound for the full sequence.
  refine eventually_atTop.mpr ?_
  -- Step 6.1: We prove that every n beyond N₁ already works.
  refine ⟨N₁, ?_⟩
  intro n hn
  -- Step 6.1.1: Use the Cauchy control between p n and the frozen subsequence element.
  have h_main : dist (p n) (p ((l : ℕ) * K)) < ε / 2 :=
    hN₁ n hn ((l : ℕ) * K) hN₁_le_lK
  -- Step 6.1.2: Combine the two ε / 2-bounds to show their sum is < ε.
  have hsum_lt :
      dist (p n) (p ((l : ℕ) * K)) + dist (p ((l : ℕ) * K)) r < ε := by
    have := add_lt_add h_main hSub_close
    simpa [add_halves] using this
  -- Step 6.1.3: Apply the triangle inequality to conclude the desired ε-bound.
  have htriangle := dist_triangle (p n) (p ((l : ℕ) * K)) r
  exact lt_of_le_of_lt htriangle hsum_lt


/-
The original formalization is weaker than the informal statement. The informal statement says:
"Suppose {p_n} is a Cauchy sequence in a metric space X, and some *subsequence* {p_{n_k}}
converges to a point p ∈ X. Prove that the full sequence {p_n} converges to p."

The original Lean theorem restricts the subsequence to the very specific arithmetic form
n ↦ p(l · n) for a fixed positive integer l : ℕ+. This only covers subsequences whose
indices form an arithmetic progression (e.g., every 2nd term, every 3rd term, etc.).
However, the informal statement allows *any* subsequence, indexed by an arbitrary strictly
increasing function φ : ℕ → ℕ (e.g., φ(k) = k², φ(k) = 2^k, or any other strictly
increasing index sequence). Since the Lean hypothesis is strictly more restrictive than
the informal hypothesis (while the conclusion is the same), the Lean theorem is logically
weaker than what the informal statement claims.

The corrected version below uses a general strictly increasing function φ : ℕ → ℕ to
index the subsequence, which faithfully captures "some subsequence converges" from the
informal statement. A strictly increasing function φ satisfies φ(n) ≥ n for all n
(hence Tendsto φ atTop atTop), making it the standard mathematical formalization of
"subsequence."
-/

theorem Rudin_exercise_3_20_corrected {X : Type*} [MetricSpace X]
  (p : ℕ → X) (φ : ℕ → ℕ) (r : X)
  (hp : CauchySeq p)
  (hφ : StrictMono φ)
  (hpl : Tendsto (p ∘ φ) atTop (𝓝 r)) :
  Tendsto p atTop (𝓝 r) := by
  -- Step 1: We apply the Mathlib lemma `tendsto_nhds_of_cauchySeq_of_subseq`.
  -- This lemma states: if u is a Cauchy sequence, f : ι → β tends to atTop,
  -- and u ∘ f converges to a, then u converges to a.
  -- We instantiate it with u := p, f := φ, p := atTop, a := r.
  exact tendsto_nhds_of_cauchySeq_of_subseq
    -- Step 1.1: The full sequence p is Cauchy (given by hypothesis `hp`).
    hp
    -- Step 1.2: The index function φ tends to atTop.
    -- Since φ is strictly monotone on ℕ, it tends to infinity.
    -- Mathlib provides `StrictMono.tendsto_atTop` for this.
    hφ.tendsto_atTop
    -- Step 1.3: The subsequence p ∘ φ converges to r (given by hypothesis `hpl`).
    hpl
