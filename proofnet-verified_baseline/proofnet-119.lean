import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

set_option checkBinderAnnotations false



/-Informal Statement

Show that if $X$ is an infinite set, it is connected in the finite complement topology.
-/

/-Informal Proof

Suppose that $A$ is a non-empty subset of $X$ that is both open and closed, i.e., $A$ and $X \backslash A$ are finite or all of $X$. Since $A$ is non-empty, $X \backslash A$ is finite. Thus $A$ cannot be finite as $X \backslash A$ is infinite, so $A$ is all of $X$. Therefore $X$ is connected.
-/

theorem Munkres_exercise_23_4 {X : Type*} [TopologicalSpace X] [CofiniteTopology X]
  (s : Set X) : Infinite s → IsConnected s := by
  sorry

/--
The formal statement above forgets to require that `X` actually carries the cofinite topology.
With the usual topology on `ℝ`, the infinite subset `ℕ` (viewed inside `ℝ`) is totally
disconnected, so the claim fails. We package the counterexample data in the record below,
which suffices to negate the universal statement.
-/
structure Exercise23_4Witness where
  X : Type
  tX : TopologicalSpace X
  cX : CofiniteTopology X
  s : Set X

/-- Counterexample to the original claim: an infinite subset in the usual topology on `ℝ`
is not connected in the cofinite sense. -/
theorem Munkres_exercise_23_4_neg :
    ∃ w : Exercise23_4Witness,
      (let _ : TopologicalSpace w.X := w.tX
       let _ : CofiniteTopology w.X := w.cX
       w.s.Infinite ∧ ¬ IsConnected w.s) := by
  classical
  -- Step 1: Work inside `ℝ` with its usual topology.
  let s : Set ℝ := Set.range fun n : ℕ => (n : ℝ)
  -- Step 1.1: Record that this subset is infinite because the embedding ℕ → ℝ is injective.
  have h_inf : s.Infinite := by
    -- Step 1.1.1: Reuse the standard injectivity of the natural inclusion ℕ → ℝ.
    have hi : Function.Injective fun n : ℕ => (n : ℝ) := by
      simpa using (Nat.cast_injective (R := ℝ))
    -- Step 1.1.2: Apply the lemma about ranges of injective maps.
    simpa [s] using Set.infinite_range_of_injective (α := ℕ) (β := ℝ) hi
  -- Step 2: Prove that `s` is not connected in ℝ with the usual topology.
  have h_not_conn : ¬ IsConnected s := by
    -- Step 2.1: Note that `s` is nonempty (witnessed by 0).
    have hs_nonempty : s.Nonempty := by
      -- Step 2.1.1: Exhibit 0 as an element of the range.
      refine ⟨0, ?_⟩; simp [s]
    -- Step 2.2: Show that `s` fails to be preconnected by constructing a separation.
    have h_pre : ¬ IsPreconnected s := by
      -- Step 2.2.1: Choose the open half-lines that isolate 0 from the other naturals.
      let u : Set ℝ := Set.Iio (1 : ℝ)
      let v : Set ℝ := Set.Ioi ((1 : ℝ) / 2)
      -- Step 2.2.2: Register that the chosen sets are open.
      have h_open_u : IsOpen u := isOpen_Iio
      have h_open_v : IsOpen v := isOpen_Ioi
      -- Step 2.2.3: Verify that every point of `s` lies in `u ∪ v`.
      have h_cover : s ⊆ u ∪ v := by
        intro x hx
        rcases hx with ⟨n, rfl⟩
        -- Step 2.2.3.1: Split on whether the natural number is 0.
        by_cases hzero : n = 0
        · -- Step 2.2.3.1.1: 0 lies in `u`.
          subst hzero
          left; simp [u]
        · -- Step 2.2.3.1.2: Every positive natural lies in `v`.
          right
          have hpos : 0 < n := Nat.pos_of_ne_zero hzero
          have hone : (1 : ℝ) ≤ (n : ℝ) := by
            -- Step 2.2.3.1.2.1: Cast the inequality `1 ≤ n` to ℝ.
            have : (1 : ℕ) ≤ n := Nat.succ_le_of_lt hpos
            exact_mod_cast this
          -- Step 2.2.3.1.2.2: Combine `1/2 < 1` with `1 ≤ n` to conclude `1/2 < n`.
          have : (1 / 2 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) hone
          simpa [v] using this
      -- Step 2.2.4: Record that both pieces of the separation meet `s`.
      have hsu : (s ∩ u).Nonempty := by
        -- Step 2.2.4.1: 0 lies in both `s` and `u`.
        refine ⟨0, ?_⟩; simp [s, u]
      have hsv : (s ∩ v).Nonempty := by
        -- Step 2.2.4.2: 1 lies in both `s` and `v`.
        refine ⟨1, ?_⟩
        constructor
        · simp [s]
        ·
          have : (1 / 2 : ℝ) < (1 : ℝ) := by norm_num
          simpa [v] using this
      -- Step 2.2.5: Show that no point of `s` lies in both `u` and `v`.
      have h_empty : ¬ (s ∩ (u ∩ v)).Nonempty := by
        -- Step 2.2.5.1: Unpack a hypothetical common point and split cases on the witness.
        rintro ⟨x, hx_s, hx_uv⟩
        rcases hx_s with ⟨n, rfl⟩
        rcases hx_uv with ⟨hx_u, hx_v⟩
        -- Step 2.2.5.1.1: Handle the case `n = 0`.
        cases n with
        | zero =>
            -- Step 2.2.5.1.1.1: `0` cannot satisfy `1/2 < 0`.
            have hx_v' : (1 / 2 : ℝ) < (0 : ℝ) := by simpa [v] using hx_v
            exact (by norm_num : ¬ ((1 / 2 : ℝ) < (0 : ℝ))) hx_v'
        | succ n =>
            -- Step 2.2.5.1.2: A positive successor cannot satisfy `(n.succ : ℝ) < 1`.
            have : (1 : ℝ) ≤ (Nat.succ n : ℝ) := by
              -- Step 2.2.5.1.2.1: Convert `1 ≤ n.succ` to the reals.
              exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
            exact not_lt_of_ge this hx_u
      -- Step 2.2.6: Conclude that the preconnectedness condition fails.
      refine fun hpre => h_empty ?_
      exact hpre u v h_open_u h_open_v h_cover hsu hsv
    -- Step 2.3: `s` is nonempty, so preconnectedness must hold if `s` were connected.
    exact fun hconn => h_pre hconn.2
  -- Step 3: Package the witness data for later use.
  refine ⟨⟨ℝ, inferInstance, CofiniteTopology.of (X := ℝ) 0, s⟩, ?_⟩
  -- Step 3.1: Activate the stored structures and provide the infinite/non-connected pair.
  dsimp only
  exact ⟨h_inf, h_not_conn⟩



/-
Problems with the original formalization:

1. `[CofiniteTopology X]` does not mean “the existing topology on `X` is
   the cofinite topology”. `CofiniteTopology X` is a type synonym for `X`
   equipped with the cofinite topology. So the original statement still has an
   arbitrary `[TopologicalSpace X]`.

2. The exercise says that the whole infinite space `X` is connected in the
   finite-complement topology. The original statement instead says that every
   infinite subset `s : Set X` is connected.

3. Therefore the original statement is not a faithful formalization of the
   textbook claim.

The corrected statement is faithful because it puts the cofinite topology on
`X` by changing the ambient type to `CofiniteTopology X`, and then proves that
the whole space `Set.univ` is connected.
-/

theorem Munkres_exercise_23_4_corrected {X : Type*} [Infinite X] :
    IsConnected (Set.univ : Set (CofiniteTopology X)) := by
  classical
  -- Step 1: Transfer the `Infinite` instance to the type synonym `CofiniteTopology X`.
  haveI : Infinite (CofiniteTopology X) := ‹Infinite X›
  -- Step 1.1: The universe of an infinite type is infinite, hence nonempty.
  have hs : (Set.univ : Set (CofiniteTopology X)).Infinite := Set.infinite_univ
  have hne : (Set.univ : Set (CofiniteTopology X)).Nonempty := hs.nonempty
  -- Step 2: Reduce the goal to preconnectedness.
  refine ⟨hne, ?_⟩
  -- Step 3: Unfold the definition of `IsPreconnected`.
  intro u v hu hv _hcover hsu hsv
  -- Step 3.1: Each open set meeting the universe has finite complement in the cofinite topology.
  have hu_nonempty : u.Nonempty := by
    rcases hsu with ⟨x, hx⟩
    exact ⟨x, hx.2⟩
  have hv_nonempty : v.Nonempty := by
    rcases hsv with ⟨x, hx⟩
    exact ⟨x, hx.2⟩
  have hu_fin : uᶜ.Finite :=
    (CofiniteTopology.isOpen_iff (X := X) (s := u)).1 hu hu_nonempty
  have hv_fin : vᶜ.Finite :=
    (CofiniteTopology.isOpen_iff (X := X) (s := v)).1 hv hv_nonempty
  -- Step 3.2: Suppose the triple intersection were empty and derive a contradiction.
  by_contra h_empty
  -- Step 3.2.1: Then every point of the universe must miss at least one of `u` or `v`.
  have h_subset : (Set.univ : Set (CofiniteTopology X)) ⊆ uᶜ ∪ vᶜ := by
    intro x hx
    by_cases hxu : x ∈ u
    · by_cases hxv : x ∈ v
      · exact (h_empty ⟨x, hx, hxu, hxv⟩).elim
      · exact Or.inr hxv
    · exact Or.inl hxu
  -- Step 3.2.2: The complement union is finite, contradicting infinitude of the universe.
  have h_fin_union : (uᶜ ∪ vᶜ).Finite := hu_fin.union hv_fin
  have h_univ_fin : (Set.univ : Set (CofiniteTopology X)).Finite := h_fin_union.subset h_subset
  exact hs h_univ_fin
