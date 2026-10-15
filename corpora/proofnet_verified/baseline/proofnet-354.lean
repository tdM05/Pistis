import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset Metric
open scoped BigOperators



/-Informal Statement

Suppose $K$ and $F$ are disjoint sets in a metric space $X, K$ is compact, $F$ is closed. Prove that there exists $\delta>0$ such that $d(p, q)>\delta$ if $p \in K, q \in F$.
-/

/-Informal Proof

Following the hint, we observe that $\rho_F(x)$ must attain its minimum value on $K$, i.e., there is some point $r \in K$ such that
$$
\rho_F(r)=\min _{q \in K} \rho_F(q) .
$$
Since $F$ is closed and $r \notin F$, it follows from Exercise $4.20$ that $\rho_F(r)>0$. Let $\delta$ be any positive number smaller than $\rho_F(r)$. Then for any $p \in F, q \in K$, we have
$$
d(p, q) \geq \rho_F(q) \geq \rho_F(r)>\delta .
$$
This proves the positive assertion.
-/

theorem Rudin_exercise_4_21a {X : Type*} [MetricSpace X]
  (K F : Set X) (hK : IsCompact K) (hF : IsClosed F) (hKF : Disjoint K F) :
  ∃ (δ : ℝ), δ > 0 ∧ ∀ (p q : X), p ∈ K → q ∈ F → dist p q > δ := by
  classical
  -- Step 1: split into the easy situation where `F` is empty, so any positive `δ` vacuously works.
  by_cases hFempty : F = ∅
  · -- Step 1.1: choose `δ = 1` (or any positive number) and note that `q ∈ F` is impossible.
    subst hFempty
    refine ⟨1, one_pos, ?_⟩
    -- Step 1.2: eliminate the impossible membership `q ∈ F` and finish the inequality.
    intro p q _ hq
    cases hq
  -- Step 2: assume `F` is nonempty from now on and deal with the subcase where `K` might be empty.
  have hFnonempty : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hFempty
  by_cases hKempty : K = ∅
  · -- Step 2.1: if `K` is empty, select `δ = 1` and exploit the impossibility `p ∈ K`.
    subst hKempty
    refine ⟨1, one_pos, ?_⟩
    -- Step 2.2: as no `p` lies in `K`, the desired inequality is vacuous.
    intro p q hp _
    cases hp
  -- Step 3: both `K` and `F` are nonempty, so we minimize `x ↦ infDist x F` on the compact set `K`.
  have hKnonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
  -- Step 3.1: apply the extreme value theorem to the continuous function `x ↦ infDist x F` on `K`.
  have hcont : Continuous fun x : X => infDist x F := continuous_infDist_pt F
  obtain ⟨x0, hx0K, hx0min⟩ := hK.exists_isMinOn hKnonempty (hcont.continuousOn)
  -- Step 3.2: `x0` cannot belong to `F` because the sets are disjoint.
  have hx0notF : x0 ∉ F := by
    intro hx0F
    exact (Set.disjoint_left.1 hKF) hx0K hx0F
  -- Step 3.3: the closedness of `F` and the non-membership of `x0` give a strictly positive `infDist`.
  have hδ0pos : 0 < infDist x0 F :=
    (hF.notMem_iff_infDist_pos hFnonempty).1 hx0notF
  -- Step 3.4: let `δ0` be the minimal value of `infDist` on `K` and take `δ = δ0 / 2` for strictness.
  set δ0 : ℝ := infDist x0 F
  refine ⟨δ0 / 2, half_pos hδ0pos, ?_⟩
  -- Step 3.5: prove that every `p ∈ K` and `q ∈ F` are at distance at least `δ0`, hence bigger than `δ0 / 2`.
  intro p q hp hq
  -- Step 3.5.1: use the minimality of `x0` to bound `infDist x0 F ≤ infDist p F`.
  have hδ0leInf : δ0 ≤ infDist p F := by
    simpa [δ0] using hx0min hp
  -- Step 3.5.2: any specific `q ∈ F` bounds `infDist p F` by `dist p q`.
  have hInfLeDist : infDist p F ≤ dist p q := infDist_le_dist_of_mem hq
  -- Step 3.5.3: combine the previous two inequalities to get `δ0 ≤ dist p q`.
  have hδ0leDist : δ0 ≤ dist p q := le_trans hδ0leInf hInfLeDist
  -- Step 3.5.4: since `δ0 / 2 < δ0`, we finish with the strict inequality.
  have hδltδ0 : δ0 / 2 < δ0 := half_lt_self hδ0pos
  exact lt_of_lt_of_le hδltδ0 hδ0leDist
