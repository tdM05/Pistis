import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

If $\left\{E_{n}\right\}$ is a sequence of closed nonempty and bounded sets in a complete metric space $X$, if $E_{n} \supset E_{n+1}$, and if $\lim _{n \rightarrow \infty} \operatorname{diam} E_{n}=0,$ then $\bigcap_{1}^{\infty} E_{n}$ consists of exactly one point.
-/

/-Informal Proof

Choose $x_n \in E_n$. (We use the axiom of choice here.) The sequence $\left\{x_n\right\}$ is a Cauchy sequence, since the diameter of $E_n$ tends to zero as $n$ tends to infinity and $E_n$ contains $E_{n+1}$. Since the metric space $X$ is complete, the sequence $x_n$ converges to a point $x$, which must belong to $E_n$ for all $n$, since $E_n$ is closed and contains $x_m$ for all $m \geq n$. There cannot be a second point $y$ in all of the $E_n$, since for any point $y \neq x$ the diameter of $E_n$ is less $\operatorname{than} d(x, y)$ for large $n$.
-/

theorem Rudin_exercise_3_21
  {X : Type*} [MetricSpace X] [CompleteSpace X]
  (E : ℕ → Set X)
  (hEcl : ∀ n, IsClosed (E n))
  (hEne : ∀ n, (E n).Nonempty)
  (hEbdd : ∀ n, Bornology.IsBounded (E n))
  (hE : ∀ n, E n ⊇ E (n + 1))
  (hE' : Tendsto (λ n => Metric.diam (E n)) atTop (𝓝 0)) :
  ∃ a, Set.iInter E = {a} := by
  classical
  -- Step 1: Use choice to pick a concrete element `x n ∈ E n` for every index `n`.
  choose x hx using hEne
  -- Step 2: Prove the nestedness lemma `E (n + m) ⊆ E n` by induction on `m`.
  have h_subset_add : ∀ n m, E (n + m) ⊆ E n := by
    intro n m
    -- Step 2.1: Handle the inductive argument on `m`.
    induction m with
    | zero =>
        -- Step 2.1.1: The case `m = 0` is immediate because `E (n + 0) = E n`.
        simp
    | succ m ih =>
        -- Step 2.1.2: The case `m + 1` uses the assumption `E k ⊇ E (k + 1)`.
        have hStep : E (n + m.succ) ⊆ E (n + m) := by
          -- Step 2.1.2.1: Rewrite the index and apply the provided monotonicity hypothesis.
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hE (n + m)
        -- Step 2.1.2.2: Chain the subset inclusions to finish the inductive step.
        exact hStep.trans ih
  -- Step 3: Translate the previous lemma into `E m ⊆ E n` whenever `n ≤ m`.
  have h_subset : ∀ {n m}, n ≤ m → E m ⊆ E n := by
    intro n m hnm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    -- Step 3.1: Apply the additive version and simplify the resulting expression.
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_subset_add n k
  -- Step 4: Record the quantitative shrinking of the diameters for later ε-control arguments.
  have h_diam_small :
      ∀ ε > 0, ∀ᶠ n in atTop, Metric.diam (E n) < ε :=
    fun ε hε => (tendsto_order.1 hE').2 ε hε
  -- Step 5: Show that the chosen sequence `(x n)` is Cauchy, using the diameter control.
  have hx_cauchy : CauchySeq x := by
    -- Step 5.1: Unfold the metric characterization of Cauchy sequences.
    refine (Metric.cauchySeq_iff).2 ?_
    intro ε hε
    -- Step 5.2: Pick an index after which all diameters are `< ε`.
    rcases (eventually_atTop.1 (h_diam_small ε hε)) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn m hm
    -- Step 5.3: Compare `n` and `m` to place both points in the same set and bound their distance.
    cases le_total n m with
    | inl hnm =>
        -- Step 5.3.1: When `n ≤ m`, both `x n` and `x m` lie in `E n`.
        have hx_n : x n ∈ E n := hx n
        have hx_m : x m ∈ E n := h_subset hnm (hx m)
        have hdist_le : dist (x n) (x m) ≤ Metric.diam (E n) :=
          Metric.dist_le_diam_of_mem (hEbdd n) hx_n hx_m
        -- Step 5.3.2: Combine the bound with `diam(E n) < ε`.
        exact lt_of_le_of_lt hdist_le (hN n hn)
    | inr hmn =>
        -- Step 5.3.3: When `m ≤ n`, a symmetric argument keeps both points inside `E m`.
        have hx_m : x m ∈ E m := hx m
        have hx_n : x n ∈ E m := h_subset hmn (hx n)
        have hdist_le : dist (x n) (x m) ≤ Metric.diam (E m) :=
          Metric.dist_le_diam_of_mem (hEbdd m) hx_n hx_m
        -- Step 5.3.4: Again use the small-diameter estimate coming from `hN`.
        exact lt_of_le_of_lt hdist_le (hN m hm)
  -- Step 6: Use completeness to get the limit point `a` together with the convergence statement.
  obtain ⟨a, ha_lim⟩ := cauchySeq_tendsto_of_complete hx_cauchy
  -- Step 7: Show that the limit point `a` belongs to every set `E n`.
  have ha_mem : ∀ n, a ∈ E n := by
    intro n
    -- Step 7.1: Every tail of the sequence eventually lies in `E n` thanks to the nesting.
    have hEventually : ∀ᶠ m in atTop, x m ∈ E n := by
      refine eventually_atTop.2 ⟨n, ?_⟩
      intro m hm
      exact h_subset hm (hx m)
    -- Step 7.2: Closedness of `E n` allows us to pass to the limit.
    exact (hEcl n).mem_of_tendsto ha_lim hEventually
  -- Step 8: Record that `a` certainly lies in the total intersection.
  have ha_inter : a ∈ Set.iInter E := Set.mem_iInter.2 ha_mem
  -- Step 9: Prove that any point in the intersection must coincide with `a`.
  have h_subset_singleton : Set.iInter E ⊆ {a} := by
    intro y hy
    -- Step 9.1: Unpack the intersection membership into pointwise membership.
    have hy_mem : ∀ n, y ∈ E n := by
      simpa [Set.mem_iInter] using hy
    -- Step 9.2: Show that `dist a y` can be made arbitrarily small.
    have hy_dist_lt : ∀ ε > 0, dist a y < ε := by
      intro ε hε
      rcases (eventually_atTop.1 (h_diam_small ε hε)) with ⟨N, hN⟩
      have haN : a ∈ E N := ha_mem N
      have hyN : y ∈ E N := hy_mem N
      have hdist_le : dist a y ≤ Metric.diam (E N) :=
        Metric.dist_le_diam_of_mem (hEbdd N) haN hyN
      exact lt_of_le_of_lt hdist_le (hN N le_rfl)
    -- Step 9.3: Deduce that `dist a y = 0` by contradiction.
    have hy_dist_zero : dist a y = 0 := by
      by_contra hdist_ne_zero
      have hpos : 0 < dist a y :=
        lt_of_le_of_ne dist_nonneg (by simpa [eq_comm] using hdist_ne_zero)
      have : dist a y < dist a y / 2 := hy_dist_lt _ (half_pos hpos)
      exact (lt_irrefl _ (lt_trans this (half_lt_self hpos)))
    -- Step 9.4: Convert the zero distance into equality and hence membership in the singleton.
    have hy_eq : a = y := by
      simpa [dist_eq_zero] using hy_dist_zero
    simp [Set.mem_singleton_iff, hy_eq.symm]
  -- Step 10: The point `a` obviously belongs to the intersection, so `{a} ⊆ ⋂ₙ E n`.
  have h_singleton_subset : {a} ⊆ Set.iInter E := by
    intro y hy
    rcases hy with rfl
    exact ha_inter
  -- Step 11: Conclude that the intersection is exactly the singleton `{a}`.
  refine ⟨a, Set.Subset.antisymm h_subset_singleton h_singleton_subset⟩
