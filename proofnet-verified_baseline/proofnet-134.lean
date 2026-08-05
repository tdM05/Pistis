import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $X$ be completely regular (separation property only). Show that $X$ is connected if and only if the Stone-Čech compactification of $X$ is connected.
-/

/-Informal Proof

The closure of a connected set is connected, so if $X$ is connected so is $\beta(X)$
Suppose $X$ is the union of disjoint open subsets $U, V \subset X$. Define the continuous map
$$
\begin{aligned}
& f: X \rightarrow\{0,1\} \\
& x \mapsto \begin{cases}0, & x \in U \\
1, & x \in V\end{cases}
\end{aligned}
$$
By the fact that $\{0,1\}$ is compact and Hausdorff we can extend $f$ to a surjective map $\bar{f}: \beta(X) \rightarrow\{0,1\}$ such that $\bar{f}^{-1}(\{0\})$ and $\bar{f}^{-1}(\{1\})$ are disjoint open sets that cover $\beta(X)$, which makes this space not-connected.
-/

theorem Munkres_exercise_38_6 {X : Type*} [TopologicalSpace X] [CompletelyRegularSpace X] :
  IsConnected (univ : Set X) ↔ IsConnected (univ : Set (StoneCech X)) := by
  -- We will show each implication separately, carefully recording every logical step.
  constructor
  · intro hX
    -- Step 1: the continuous image of a connected set is connected.
    -- Here the set is `univ : Set X` and the map is `stoneCechUnit`.
    have hImage : IsConnected (stoneCechUnit '' (univ : Set X)) := by
      -- Step 1.1: apply the `IsConnected.image` lemma with the global continuity of `stoneCechUnit`.
      exact hX.image _ (continuous_stoneCechUnit.continuousOn)
    -- Step 2: the closure of a connected set remains connected.
    have hClosure : IsConnected (closure (stoneCechUnit '' (univ : Set X))) :=
      hImage.closure
    -- Step 3: rewrite the closure in terms of the range to use the density lemma conveniently.
    have hClosureRange :
        IsConnected (closure (range (stoneCechUnit : X → StoneCech X))) := by
      -- Step 3.1: `stoneCechUnit '' univ` is definitionally the range of `stoneCechUnit`.
      simpa [Set.image_univ] using hClosure
    -- Step 4: density tells us that this closure is the whole Stone–Čech space.
    have hClosureEq :
        closure (range (stoneCechUnit : X → StoneCech X)) = (univ : Set (StoneCech X)) :=
      denseRange_stoneCechUnit.closure_range
    -- Step 5: conclude connectedness of `univ : Set (StoneCech X)`.
    simpa [hClosureEq] using hClosureRange
  · intro hBeta
    -- We now prove that connectedness of the Stone–Čech compactification forces `X` to be connected.
    classical
    -- Step 1: interpret the hypothesis as a `ConnectedSpace` instance for convenience.
    have hBetaConnSpace : ConnectedSpace (StoneCech X) :=
      (connectedSpace_iff_univ).2 hBeta
    -- Step 2: argue by contradiction, assuming `X` were not connected.
    by_contra hXConn
    -- Step 2.1: translate the negation into the absence of a `ConnectedSpace` structure.
    have hNotConnSpace : ¬ ConnectedSpace X := by
      intro hConn
      exact hXConn ((connectedSpace_iff_univ).1 hConn)
    -- Step 2.2: establish that `X` is nonempty (needed to invoke the clopen characterization).
    have hNonemptyX : Nonempty X := by
      -- Step 2.2.1: the connectedness of `StoneCech X` yields a nonempty underlying set.
      have hNonemptySC : (univ : Set (StoneCech X)).Nonempty := hBeta.nonempty
      -- Step 2.2.2: if the range of `stoneCechUnit` were empty, its closure would be empty, contradicting density.
      have hDense : DenseRange (stoneCechUnit : X → StoneCech X) := denseRange_stoneCechUnit
      have hRangeNonempty : (range (stoneCechUnit : X → StoneCech X)).Nonempty := by
        by_contra hEmpty
        -- Step 2.2.2.1: convert the negated nonempty statement into an equality with the empty set.
        have hRangeEq : range (stoneCechUnit : X → StoneCech X) =
            (∅ : Set (StoneCech X)) := Set.not_nonempty_iff_eq_empty.mp hEmpty
        -- Step 2.2.2.2: take closures on both sides; the closure of the empty set is still empty.
        have hClosureEmpty :
            closure (range (stoneCechUnit : X → StoneCech X)) =
              (∅ : Set (StoneCech X)) := by
          simp [hRangeEq]
        -- Step 2.2.2.3: density tells us the closure must be the whole space, contradiction.
        have hClosureAll := hDense.closure_range
        have hUnivEqEmpty : (univ : Set (StoneCech X)) = (∅ : Set (StoneCech X)) := by
          calc
            (univ : Set (StoneCech X))
                = closure (range (stoneCechUnit : X → StoneCech X)) :=
              hClosureAll.symm
            _ = (∅ : Set (StoneCech X)) := hClosureEmpty
        -- Step 2.2.2.4: but `univ` is known to be nonempty.
        have hContr : False := by
          have hSC := hNonemptySC
          -- specializing the nonempty proof to the contradictory equality.
          simp [hUnivEqEmpty] at hSC
        exact hContr.elim
      -- Step 2.2.3: extract an explicit element of `X` from the nonempty range.
      rcases hRangeNonempty with ⟨_, ⟨x0, rfl⟩⟩
      exact ⟨x0⟩
    -- Step 3: by failing the clopen characterization, obtain a nontrivial clopen subset of `X`.
    have hBadClopen :
        ¬ ∀ t : Set X, IsClopen t → t = (∅ : Set X) ∨ t = (univ : Set X) := by
      intro hAll
      -- If every clopen were trivial, `X` would be connected, contradicting `hNotConnSpace`.
      apply hNotConnSpace
      exact (connectedSpace_iff_clopen).2 ⟨hNonemptyX, hAll⟩
    -- Step 3.1: pick a specific clopen set witnessing the failure.
    obtain ⟨s, hsFail⟩ := not_forall.mp hBadClopen
    -- Step 3.2: show that this witness `s` is indeed clopen.
    have hsClopen : IsClopen s := by
      by_contra h
      exact hsFail (by intro hs; exact (h hs).elim)
    -- Step 3.3: `s` is nontrivial (neither empty nor the whole space).
    have hsNontrivial : ¬ (s = (∅ : Set X) ∨ s = (univ : Set X)) := by
      intro hTriv
      exact hsFail (by intro _; exact hTriv)
    have hsNeEmpty : s ≠ (∅ : Set X) := by
      intro h
      exact hsNontrivial (Or.inl h)
    have hsNeUniv : s ≠ (univ : Set X) := by
      intro h
      exact hsNontrivial (Or.inr h)
    -- Step 4: build a nonconstant continuous map `f : X → Bool` using the clopen set.
    let f : X → Bool := s.boolIndicator
    have hfCont : Continuous f :=
      (continuous_boolIndicator_iff_isClopen s).2 hsClopen
    -- Step 4.1: pick one point inside `s`.
    have hs_nonempty : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hsNeEmpty
    rcases hs_nonempty with ⟨x, hx⟩
    -- Step 4.2: pick one point outside `s` (possible because `s ≠ univ`).
    have hNotAll : ¬ ∀ y : X, y ∈ s := by
      -- `s ≠ univ` translates to the existence of an element outside `s`.
      simpa [Set.eq_univ_iff_forall] using hsNeUniv
    obtain ⟨y, hy⟩ := not_forall.mp hNotAll
    -- Step 4.3: record the distinct Boolean values of `f` at these two points.
    have hfx : f x = true := (Set.mem_iff_boolIndicator (s := s) x).mp hx
    have hfy : f y = false := (Set.notMem_iff_boolIndicator (s := s) y).mp hy
    have hDiff : f x ≠ f y := by
      -- true ≠ false is immediate by computation.
      simp [hfx, hfy]
    -- Step 5: extend `f` to the Stone–Čech compactification using its universal property.
    let g : StoneCech X → Bool := stoneCechExtend hfCont
    have hgCont : Continuous g := continuous_stoneCechExtend hfCont
    -- Step 5.1: the extension agrees with `f` on the canonical dense copy of `X`.
    have hgx : g (stoneCechUnit x) = true := by
      -- evaluate the extension at `x` and substitute the known value of `f x`.
      calc
        g (stoneCechUnit x) = f x := (stoneCechExtend_stoneCechUnit hfCont x)
        _ = true := hfx
    have hgy : g (stoneCechUnit y) = false := by
      calc
        g (stoneCechUnit y) = f y := (stoneCechExtend_stoneCechUnit hfCont y)
        _ = false := hfy
    -- Step 5.2: these two distinct values show that `g` is nonconstant.
    have hValuesDifferent :
        g (stoneCechUnit x) ≠ g (stoneCechUnit y) := by
      simp [hgx, hgy]
    -- Step 6: connectedness of the domain `StoneCech X` forces any continuous map to `Bool` to be constant.
    -- We derive a contradiction by exhibiting a separation using `g`.
    -- Step 6.1: consider the standard open (and closed) singletons in `Bool`.
    let U : Set Bool := {true}
    let V : Set Bool := {false}
    have hUopen : IsOpen U := by simp [U]
    have hVopen : IsOpen V := by simp [V]
    -- Step 6.2: the entire image of `g` is contained in `U ∪ V`, which is all of `Bool`.
    have hCover : g '' (univ : Set (StoneCech X)) ⊆ U ∪ V := by
      intro b hb
      cases b <;> simp [U, V]
    -- Step 6.3: both halves of the proposed separation meet the image (witnessed by `x` and `y`).
    have hU_nonempty :
        (g '' (univ : Set (StoneCech X)) ∩ U).Nonempty := by
      refine ⟨g (stoneCechUnit x), ?_⟩
      constructor
      · exact ⟨stoneCechUnit x, trivial, rfl⟩
      · simp [U, hgx]
    have hV_nonempty :
        (g '' (univ : Set (StoneCech X)) ∩ V).Nonempty := by
      refine ⟨g (stoneCechUnit y), ?_⟩
      constructor
      · exact ⟨stoneCechUnit y, trivial, rfl⟩
      · simp [V, hgy]
    -- Step 6.4: apply preconnectedness of the image of `g` to the open sets `U` and `V`.
    have hImagePreconn :
        IsPreconnected (g '' (univ : Set (StoneCech X))) :=
      (hBeta.image g hgCont.continuousOn).isPreconnected
    have hInter := hImagePreconn U V hUopen hVopen hCover hU_nonempty hV_nonempty
    -- Step 6.5: but `U ∩ V` is empty in `Bool`, so the intersection must be empty—a contradiction.
    have hUV_empty : U ∩ V = (∅ : Set Bool) := by
      ext b; simp [U, V]
    have : False := by
      -- The preconnectedness conclusion says the intersection is nonempty; we show it is empty.
      have hNonemptyInter : (g '' (univ : Set (StoneCech X)) ∩ (U ∩ V)).Nonempty := hInter
      simp [hUV_empty] at hNonemptyInter
    exact this.elim
