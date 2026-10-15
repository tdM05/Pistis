import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

/-!

The auxiliary lemma `Icc_subset_of_preconnected_real` encapsulates the basic fact that
for a preconnected subset of the reals containing two ordered points, the whole closed
interval between them stays inside the set.  This is the engine behind the main proof,
where we apply it to the image of a connected metric space under the distance-from-a-point
map.
-/

private lemma Icc_subset_of_preconnected_real
    {S : Set ℝ} (hS : IsPreconnected S) {a b : ℝ}
    (ha : a ∈ S) (hb : b ∈ S) :
    Set.Icc a b ⊆ S := by
  classical
  intro t ht
  -- Step 1: Record the endpoint inequalities carried by the membership `t ∈ [a, b]`.
  rcases ht with ⟨hat, htb⟩
  -- Step 2: If `t` coincides with one of the endpoints, use the corresponding hypothesis.
  by_cases hta : t = a
  · -- Step 2.1: The left endpoint already lies in `S`, so the claim is immediate.
    simpa [hta] using ha
  by_cases htb' : t = b
  · -- Step 2.2: The right endpoint already lies in `S`, so we are done as well.
    simpa [htb'] using hb
  -- Step 3: Reduce to the genuinely interior case `a < t < b`.
  have hat_lt : a < t := lt_of_le_of_ne hat (ne_comm.mp hta)
  have htb_lt : t < b := lt_of_le_of_ne htb htb'
  -- Step 4: Assume for contradiction that `t` falls outside of `S`.
  by_contra hnot
  -- Step 5: Show that every point of `S` must lie either to the left or to the right of `t`.
  have hcover :
      S ⊆ Set.Iio t ∪ Set.Ioi t := by
    intro z hz
    -- Step 5.1: Exclude the possibility that `z = t`, which would contradict `hnot`.
    have hz_ne : z ≠ t := by
      intro hz_eq
      exact hnot (by simpa [hz_eq] using hz)
    -- Step 5.2: Use trichotomy on the reals to locate `z` relative to `t`.
    rcases lt_or_gt_of_ne hz_ne with hz_lt | hz_gt
    · exact Or.inl hz_lt
    · exact Or.inr hz_gt
  -- Step 6: Exhibit that both sides of the supposed separation actually meet `S`.
  have hleft : (S ∩ Set.Iio t).Nonempty := by
    refine ⟨a, ?_⟩
    -- Step 6.1: The point `a` lies in `S` and strictly to the left of `t`.
    exact ⟨ha, hat_lt⟩
  have hright : (S ∩ Set.Ioi t).Nonempty := by
    refine ⟨b, ?_⟩
    -- Step 6.2: The point `b` lies in `S` and strictly to the right of `t`.
    exact ⟨hb, htb_lt⟩
  -- Step 7: Apply preconnectedness to derive a point simultaneously on both sides of `t`.
  obtain ⟨z, hz⟩ :=
    hS _ _ isOpen_Iio isOpen_Ioi hcover hleft hright
  rcases hz with ⟨hzS, hz⟩
  rcases hz with ⟨hzlt, hzgt⟩
  -- Step 8: Contradict the strict order property `¬ z < z` using `z < t < z`.
  exact (lt_irrefl z) (lt_trans hzlt hzgt)

/-Informal Statement

Show that a connected metric space having more than one point is uncountable.
-/

/-Informal Proof

The distance function $d: X \times X \rightarrow \mathbb{R}$ is continuous by Exercise 20.3(a), so given $x \in X$, the function $d_x: X \rightarrow \mathbb{R}$ given by $d_x(y)=d(x, y)$ is continuous by Exercise 19.11. Since $X$ is connected, the image $d_x(X)$ is a connected subspace of $\mathbb{R}$, and contains 0 since $d_x(x)=0$. Thus, if $y \in X$ and $y \neq x$, then $d_x(X)$ contains the set $[0, \delta]$, where $\delta=d_x(y)>0$. Therefore $X$ must be uncountable.
-/

theorem Munkres_exercise_27_4
  {X : Type*} [MetricSpace X] [ConnectedSpace X] (hX : ∃ x y : X, x ≠ y) :
  ¬ Countable (univ : Set X) := by
  classical
  -- Step 1: Suppose for contradiction that the whole space is countable.
  intro hcount
  -- Step 2: Choose two distinct points in the connected metric space.
  obtain ⟨x, y, hxy⟩ := hX
  -- Step 3: Denote the positive distance between the chosen points.
  set δ : ℝ := dist x y
  have hδpos : 0 < δ := dist_pos.mpr hxy
  -- Step 4: Consider the distance-from-`x` map and the image of the whole space.
  let f : X → ℝ := fun z => dist x z
  have hf_cont : Continuous f := by
    -- Step 4.1: Continuity follows from the general continuity of the distance function.
    simpa using (continuous_const.dist (continuous_id : Continuous fun z : X => z))
  let S : Set ℝ := f '' (univ : Set X)
  -- Step 5: Record that the image `S` is preconnected because `X` is connected.
  have hS_pre : IsPreconnected S := by
    -- Step 5.1: Apply preconnectedness preservation under continuous images.
    simpa [S] using
      (isPreconnected_univ : IsPreconnected (univ : Set X)).image f hf_cont.continuousOn
  -- Step 6: Identify the two specific points of `S` lying at distances `0` and `δ`.
  have h_zero_in : (0 : ℝ) ∈ S := by
    -- Step 6.1: The point `x` maps to `0` under the distance-from-`x` map.
    refine ⟨x, trivial, ?_⟩
    simp [f]
  have h_delta_in : δ ∈ S := by
    -- Step 6.2: The point `y` maps to the distance `δ`.
    refine ⟨y, trivial, ?_⟩
    simp [f, δ]
  -- Step 7: The entire interval `[0, δ]` sits inside `S` by preconnectedness.
  have hinterval :
      Set.Icc (0 : ℝ) δ ⊆ S :=
    Icc_subset_of_preconnected_real hS_pre h_zero_in h_delta_in
  -- Step 8: Use countability of `X` to deduce countability of `S` and hence of the interval.
  have hS_countable : S.Countable := Set.Countable.image hcount f
  have hIcc_countable : (Set.Icc (0 : ℝ) δ).Countable :=
    Set.Countable.mono hinterval hS_countable
  -- Step 9: Translate the countability of `[0, δ]` into the inequality `δ ≤ 0`.
  have hδ_le_zero : δ ≤ 0 :=
    (Cardinal.Real.Icc_countable_iff).mp hIcc_countable
  -- Step 10: Contradict the positivity of `δ`.
  exact (not_le.mpr hδpos) hδ_le_zero
