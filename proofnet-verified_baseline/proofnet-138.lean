import Mathlib

open Filter Real Function Set Metric
open scoped Topology



/-Informal Statement

Show that if $S$ is connected, it is not true in general that its interior is connected.
-/

/-Informal Proof

Consider $X=\mathbb{R}^2$ and
$$
A=([-2,0] \times[-2,0]) \cup([0,2] \times[0,2])
$$
which is connected, while $\operatorname{int}(A)$ is not connected.
To see this consider the continuous function $f: \mathbb{R}^2 \rightarrow \mathbb{R}$ is defined by $f(x, y)=x+y$. Let $U=f^{-1}(0,+\infty)$ which is open in $\mathbb{R}^2$ and so $U \cap \operatorname{int}(A)$ is open in $\operatorname{int}(A)$. Also, since $(0,0) \notin \operatorname{int}(A)$, so for all $(x, y) \in \operatorname{int}(A), f(x, y) \neq 0$ and $U \cap \operatorname{int}(A)=f^{-1}[0,+\infty) \cap \operatorname{int}(A)$ is closed in $\operatorname{int}(A)$. Furthermore, $(1,1)=f^{-1}(2) \in U \cap \operatorname{int}(A)$ shows that $U \cap \operatorname{int}(A) \neq \emptyset$ while $(-1,-1) \in \operatorname{int}(A)$ and $(-1,-1) \notin U$ shows that $U \cap \operatorname{int}(A) \neq \operatorname{int}(A)$.
-/

theorem Pugh_exercise_2_57 {X : Type*} [TopologicalSpace X]
  : ∃ (S : Set X), IsConnected S ∧ ¬ IsConnected (interior S) := by
  sorry

/-
Counterexample strategy: specialise the (incorrect) universal claim to the one-point
space `Unit`. Any connected subset of `Unit` must equal the whole space, and that whole
space obviously has connected interior. This contradicts the desired property, so the
original statement cannot hold without extra hypotheses.
-/
namespace Proofnet138

open Classical

/-!
We begin with two structural lemmas about subsets of the one-point space. The comments in
each proof are numbered so that every inference step is explicitly documented, as
required.
-/

lemma unit_connected_subset_eq_univ {S : Set Unit} (hS : IsConnected S) :
    S = (Set.univ : Set Unit) := by
  -- Step 1: `IsConnected` implies `S` is nonempty, so obtain a point of `S`.
  obtain ⟨x, hx⟩ := hS.nonempty
  -- Step 2: The only element of `Unit` is `()`, so rewrite the witness and record membership.
  cases x
  have hstar : (()) ∈ S := by simpa using hx
  -- Step 3: Prove `S = univ` by extensionality on the unique element of `Unit`.
  ext u
  -- Step 3.1: Any element of `S` is automatically in `univ`.
  · cases u
    constructor
    · intro _
      simp
    · intro _
      simpa using hstar

lemma isConnected_univ_unit : IsConnected (Set.univ : Set Unit) := by
  -- Step 1: Identify `Set.univ` on `Unit` with the singleton `{()}`.
  have hsingleton : (Set.univ : Set Unit) = ({()} : Set Unit) := by
    ext u
    cases u
    simp
  -- Step 2: Singletons are connected, so transfer the fact to `Set.univ`.
  simpa [hsingleton] using (isConnected_singleton (x := ()))

/--
The original universal statement fails. We build a counterexample by taking `X = Unit` and
observing that the interior of any connected subset is still connected, contradicting the
required negation.
-/
theorem Pugh_exercise_2_57_neg :
    ¬ (∀ (X : Type) [TopologicalSpace X],
        ∃ S : Set X, IsConnected S ∧ ¬ IsConnected (interior S)) := by
  -- Step 1: Assume the universal property and derive a contradiction.
  intro h
  -- Step 2: Specialise the hypothesis to the one-point space `Unit`.
  classical
  obtain ⟨S, hS_conn, hint_disconn⟩ := h (X := Unit)
  -- Step 3: Show that any connected subset of `Unit` equals the whole space.
  have hS_eq : S = (Set.univ : Set Unit) := unit_connected_subset_eq_univ hS_conn
  -- Step 4: Compute the interior (still `univ`) and note it is connected.
  have hint_conn : IsConnected (interior S) := by
    -- Step 4.1: Rewrite the interior using `S = univ`.
    have hint_eq : interior S = (Set.univ : Set Unit) := by simp [hS_eq]
    -- Step 4.2: Transfer the connectivity of `Set.univ` to `interior S`.
    simpa [hint_eq] using isConnected_univ_unit
  -- Step 5: Contradict the assumption that the interior is disconnected.
  exact hint_disconn hint_conn

/--
Corrected version: within the concrete space `ℝ × ℝ` there *does* exist a connected set whose
interior is disconnected. We exhibit the union of two closed squares meeting at the origin.
-/
theorem Pugh_exercise_2_57_corrected :
    ∃ S : Set (ℝ × ℝ), IsConnected S ∧ ¬ IsConnected (interior S) := by
  classical
  -- Step 1: Define the two closed squares and their union `S`.
  let squareNeg : Set (ℝ × ℝ) :=
    (Set.Icc (-2 : ℝ) 0) ×ˢ (Set.Icc (-2 : ℝ) 0)
  let squarePos : Set (ℝ × ℝ) :=
    (Set.Icc (0 : ℝ) 2) ×ˢ (Set.Icc (0 : ℝ) 2)
  let S := squareNeg ∪ squarePos
  -- Step 2: Each closed square is connected as a product of connected intervals.
  have hneg_conn : IsConnected squareNeg := by
    -- Step 2.1: The interval `[-2, 0]` is connected.
    have hinterval : IsConnected (Set.Icc (-2 : ℝ) 0) := by
      -- Step 2.1.1: Provide the order inequality needed by `isConnected_Icc`.
      have hle : (-2 : ℝ) ≤ 0 := by norm_num
      -- Step 2.1.2: Apply the standard connectivity result for closed intervals.
      simpa using isConnected_Icc hle
    -- Step 2.2: Form the product of the two identical connected intervals.
    simpa [squareNeg] using hinterval.prod hinterval
  have hpos_conn : IsConnected squarePos := by
    -- Step 2.3: The interval `[0, 2]` is connected for the same reason.
    have hinterval : IsConnected (Set.Icc (0 : ℝ) 2) := by
      have hle : (0 : ℝ) ≤ 2 := by norm_num
      simpa using isConnected_Icc hle
    -- Step 2.4: Take the product of the two `[0, 2]` intervals.
    simpa [squarePos] using hinterval.prod hinterval
  -- Step 3: The two squares meet at `(0, 0)`, ensuring the union is connected.
  have hint : (squareNeg ∩ squarePos).Nonempty := by
    -- Step 3.1: Exhibit the common vertex `(0, 0)` explicitly.
    refine ⟨⟨(0 : ℝ), 0⟩, ?_, ?_⟩
    · -- Step 3.1.1: `(0, 0)` lies in the negative square.
      simp [squareNeg]
    · -- Step 3.1.2: `(0, 0)` also lies in the positive square.
      simp [squarePos]
  have hS_conn : IsConnected S :=
    -- Step 3.2: Use `IsConnected.union` with the nonempty intersection.
    (IsConnected.union hint hneg_conn hpos_conn)
  -- Step 4: Identify the interiors of the squares and embed them into `interior S`.
  let U : Set (ℝ × ℝ) := (Set.Ioo (-2 : ℝ) 0) ×ˢ (Set.Ioo (-2 : ℝ) 0)
  let V : Set (ℝ × ℝ) := (Set.Ioo (0 : ℝ) 2) ×ˢ (Set.Ioo (0 : ℝ) 2)
  have hint_neg : interior squareNeg = U := by
    -- Step 4.1: Use the product-interior formula and the known interior of a closed interval.
    simpa [squareNeg, U, interior_Icc] using
      (interior_prod_eq (Set.Icc (-2 : ℝ) 0) (Set.Icc (-2 : ℝ) 0))
  have hint_pos : interior squarePos = V := by
    -- Step 4.2: Apply the same computation to the positive square.
    simpa [squarePos, V, interior_Icc] using
      (interior_prod_eq (Set.Icc (0 : ℝ) 2) (Set.Icc (0 : ℝ) 2))
  have hUsubset : U ⊆ interior S := by
    -- Step 4.3: Interior is monotone with respect to inclusion.
    have hsubset : squareNeg ⊆ S := by
      intro x hx
      exact Or.inl hx
    have := interior_mono hsubset
    simpa [hint_neg]
  have hVsubset : V ⊆ interior S := by
    -- Step 4.4: Repeat the monotonicity argument for the positive square.
    have hsubset : squarePos ⊆ S := by
      intro x hx
      exact Or.inr hx
    have := interior_mono hsubset
    simpa [hint_pos]
  -- Step 5: Record explicit interior points supplied by the two squares.
  have hx_neg_mem : (⟨-1, -1⟩ : ℝ × ℝ) ∈ interior S := by
    -- Step 5.1: Use that `(-1, -1)` lies in the interior of the negative square.
    have : (⟨-1, -1⟩ : ℝ × ℝ) ∈ U := by simp [U]
    exact hUsubset this
  have hx_pos_mem : (⟨1, 1⟩ : ℝ × ℝ) ∈ interior S := by
    -- Step 5.2: Similarly, `(1, 1)` belongs to the interior of the positive square.
    have : (⟨1, 1⟩ : ℝ × ℝ) ∈ V := by simp [V]
    exact hVsubset this
  -- Step 6: Introduce the open half-spaces that will separate the interior.
  let leftHalf : Set (ℝ × ℝ) := (Set.Iio (0 : ℝ)) ×ˢ Set.univ
  let rightHalf : Set (ℝ × ℝ) := (Set.Ioi (0 : ℝ)) ×ˢ Set.univ
  have hopen_left : IsOpen leftHalf := IsOpen.prod isOpen_Iio isOpen_univ
  have hopen_right : IsOpen rightHalf := IsOpen.prod isOpen_Ioi isOpen_univ
  -- Step 6.1: Any interior point must lie in exactly one of the two half-spaces.
  have hcover : interior S ⊆ leftHalf ∪ rightHalf := by
    intro x hx
    have hxS : x ∈ S := interior_subset hx
    classical
    rcases hxS with hxneg | hxpos
    · -- Step 6.1.1: Show the first coordinate is strictly negative in this case.
      rcases hxneg with ⟨hxneg₁, hxneg₂⟩
      have hxle : x.1 ≤ 0 := (Set.mem_Icc.mp hxneg₁).2
      have hxne : x.1 ≠ 0 := by
        intro hxzero
        obtain ⟨ε, hεpos, hball_int⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
        set δ := ε / 2 with hδdef
        have hδpos : 0 < δ := by simpa [δ, hδdef] using half_pos hεpos
        have hδlt : δ < ε := by simpa [δ, hδdef] using half_lt_self hεpos
        let y : ℝ × ℝ := ⟨δ, x.2 - δ⟩
        have hy_ball : y ∈ Metric.ball x ε := by
          have hy_dist : dist x y = δ := by
            simp [Prod.dist_eq, y, hxzero, Real.dist_eq, abs_of_nonneg hδpos.le]
          have hy_dist' : dist y x = δ := by simp [dist_comm, hy_dist]
          simp [Metric.mem_ball, hy_dist', hδlt]
        have hball_subset : Metric.ball x ε ⊆ S :=
          fun z hz => interior_subset (hball_int hz)
        have hx2le : x.2 ≤ 0 := (Set.mem_Icc.mp hxneg₂).2
        have hy_neg : y.2 < 0 := by
          have hle : y.2 ≤ -δ := by
            have : x.2 - δ ≤ 0 - δ := sub_le_sub_right hx2le δ
            simpa [y, δ, hδdef] using this
          have : (-δ : ℝ) < 0 := by
            have : δ > 0 := hδpos
            linarith
          exact lt_of_le_of_lt hle this
        have hy_not_neg : y ∉ squareNeg := by
          intro hmem
          simp only [squareNeg, Set.mem_prod, Set.mem_Icc, y] at hmem
          linarith [hmem.1.2]
        have hy_not_pos : y ∉ squarePos := by
          simp [squarePos, y, not_le_of_gt hy_neg]
        have hy_not : y ∉ S := by
          intro hyS
          cases hyS with
          | inl hy => exact hy_not_neg hy
          | inr hy => exact hy_not_pos hy
        exact hy_not (hball_subset hy_ball)
      have hxlt : x.1 < 0 := lt_of_le_of_ne' hxle hxne.symm
      exact Or.inl (by simp [leftHalf, hxlt])
    · -- Step 6.1.2: Symmetric reasoning shows the first coordinate is positive.
      rcases hxpos with ⟨hxpos₁, hxpos₂⟩
      have hxge : 0 ≤ x.1 := (Set.mem_Icc.mp hxpos₁).1
      have hxne : x.1 ≠ 0 := by
        intro hxzero
        obtain ⟨ε, hεpos, hball_int⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
        set δ := ε / 2 with hδdef
        have hδpos : 0 < δ := by simpa [δ, hδdef] using half_pos hεpos
        have hδlt : δ < ε := by simpa [δ, hδdef] using half_lt_self hεpos
        let y : ℝ × ℝ := ⟨-δ, x.2 + δ⟩
        have hy_ball : y ∈ Metric.ball x ε := by
          have hy_dist : dist x y = δ := by
            simp [Prod.dist_eq, y, hxzero, Real.dist_eq, abs_of_nonneg hδpos.le]
          have hy_dist' : dist y x = δ := by simp [dist_comm, hy_dist]
          simp [Metric.mem_ball, hy_dist', hδlt]
        have hball_subset : Metric.ball x ε ⊆ S :=
          fun z hz => interior_subset (hball_int hz)
        have hx2ge : 0 ≤ x.2 := (Set.mem_Icc.mp hxpos₂).1
        have hy_pos : 0 < y.2 := by
          have hge : δ ≤ y.2 := by
            have : δ ≤ δ + x.2 := le_add_of_nonneg_right hx2ge
            simpa [y, δ, hδdef, add_comm] using this
          exact lt_of_lt_of_le hδpos hge
        have hy_not_neg : y ∉ squareNeg := by
          simp [squareNeg, y, not_le_of_gt hy_pos]
        have hy_not_pos : y ∉ squarePos := by
          intro hmem
          simp only [squarePos, Set.mem_prod, Set.mem_Icc, y] at hmem
          linarith [hmem.1.1]
        have hy_not : y ∉ S := by
          intro hyS
          cases hyS with
          | inl hy => exact hy_not_neg hy
          | inr hy => exact hy_not_pos hy
        exact hy_not (hball_subset hy_ball)
      have hxgt : 0 < x.1 := lt_of_le_of_ne' hxge hxne
      exact Or.inr (by simp [rightHalf, hxgt])
  -- Step 7: The half-spaces are disjoint and both meet the interior of `S`.
  have hdisjoint : Disjoint leftHalf rightHalf := by
    refine Set.disjoint_left.2 ?_
    intro x hxL hxR
    rcases hxL with ⟨hxL, _⟩
    rcases hxR with ⟨hxR, _⟩
    exact (lt_irrefl (0 : ℝ)) (lt_trans hxR hxL)
  have hleft_nonempty : (interior S ∩ leftHalf).Nonempty := by
    refine ⟨⟨-1, -1⟩, ?_⟩
    exact ⟨hx_neg_mem, by simp [leftHalf]⟩
  have hright_nonempty : (interior S ∩ rightHalf).Nonempty := by
    refine ⟨⟨1, 1⟩, ?_⟩
    exact ⟨hx_pos_mem, by simp [rightHalf]⟩
  -- Step 8: Use the definition of `IsPreconnected` with the separating half-spaces.
  have hint_not_pre : ¬ IsPreconnected (interior S) := by
    intro hint_pre
    have hcontr :=
      hint_pre leftHalf rightHalf hopen_left hopen_right hcover hleft_nonempty hright_nonempty
    rcases hcontr with ⟨x, hx⟩
    rcases hx with ⟨_, hxLR⟩
    rcases hxLR with ⟨hxL, hxR⟩
    exact (Set.disjoint_left.1 hdisjoint) hxL hxR
  -- Step 9: Convert the failure of preconnectedness into disconnectedness.
  have hint_not_conn : ¬ IsConnected (interior S) := by
    intro hint_conn
    exact hint_not_pre hint_conn.isPreconnected
  -- Step 10: Package the witness `S` with both desired properties.
  refine ⟨S, hS_conn, ?_⟩
  exact hint_not_conn

end Proofnet138
