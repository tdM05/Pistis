import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

abbrev I : Set ℝ := Icc 0 1

/-Informal Statement

Let $f \colon X \rightarrow X$ be continuous. Show that if $X = [0, 1]$, there is a point $x$ such that $f(x) = x$. (The point $x$ is called a fixed point of $f$.)
-/

/-Informal Proof

If $f(0)=0$ or $f(1)=1$ we are done, so suppose $f(0)>0$ and $f(1)<1$. Let $g:[0,1] \rightarrow[0,1]$ be given by $g(x)=f(x)-x$. Then $g$ is continuous, $g(0)>0$ and $g(1)<0$. Since $[0,1]$ is connected and $g(1)<0<g(0)$, by the intermediate value theorem there exists $x \in(0,1)$ such that $g(x)=0$, that is, such that $f(x)=x$.
-/

theorem Munkres_exercise_24_3a (f : I → I) (hf : Continuous f) :
  ∃ (x : I), f x = x := by
  classical
  -- Step 1: Choose the endpoints `a = 0` and `b = 1` as explicit elements of the subtype `I`.
  let a : I := ⟨0, by
    -- Step 1.1: Verify that `0` lies in `[0, 1]`.
    exact ⟨le_rfl, zero_le_one⟩
  ⟩
  let b : I := ⟨1, by
    -- Step 1.2: Verify that `1` also lies in `[0, 1]`.
    exact ⟨zero_le_one, le_rfl⟩
  ⟩
  -- Step 2: Define the auxiliary function `g(x) = f(x) - x` taking values in `ℝ`.
  let g : I → ℝ := fun x => (f x : ℝ) - (x : ℝ)
  -- Step 2.1: Record that `g` is continuous as the difference of two continuous real-valued maps.
  have hg_cont : Continuous g := by
    -- Step 2.1.1: The map `x ↦ (f x : ℝ)` is continuous via the inclusion `I ↪ ℝ`.
    have h_toReal : Continuous fun x : I => (f x : ℝ) :=
      continuous_subtype_val.comp hf
    -- Step 2.1.2: Subtract the identity inclusion to obtain continuity of `g`.
    exact h_toReal.sub continuous_subtype_val
  -- Step 3: Control the sign of `g` at the endpoints.
  -- Step 3.1: Show that `g(a) ≥ 0`, i.e., `f(a) ≥ 0`.
  have hga_nonneg : 0 ≤ g a := by
    -- Step 3.1.1: `f a` belongs to `[0, 1]`, so extract its lower bound.
    have hfa_mem : ((f a : ℝ) ∈ I) := (f a).property
    have hfa_lower : 0 ≤ (f a : ℝ) := (Set.mem_Icc.mp hfa_mem).1
    -- Step 3.1.2: Rewrite `g a` in terms of `f a` and conclude.
    simpa [g, a] using hfa_lower
  -- Step 3.2: Show that `g(b) ≤ 0`, i.e., `f(b) ≤ 1`.
  have hgb_nonpos : g b ≤ 0 := by
    -- Step 3.2.1: Again record that `f b` takes values in `[0, 1]`.
    have hfb_mem : ((f b : ℝ) ∈ I) := (f b).property
    have hfb_upper : (f b : ℝ) ≤ 1 := (Set.mem_Icc.mp hfb_mem).2
    -- Step 3.2.2: Rewrite `g b = (f b) - 1` and use the recorded bound.
    have : (f b : ℝ) - 1 ≤ 0 := sub_nonpos.mpr hfb_upper
    simpa [g, b] using this
  -- Step 4: Apply the intermediate value theorem (in the form `mem_range_of_exists_le_of_exists_ge`)
  --         to obtain a point `x` with `g x = 0`.
  have hZeroInRange :
      (0 : ℝ) ∈ Set.range g :=
    mem_range_of_exists_le_of_exists_ge hg_cont
      ⟨b, hgb_nonpos⟩ ⟨a, hga_nonneg⟩
  -- Step 4.1: Extract the witness `x` with `g x = 0`.
  rcases hZeroInRange with ⟨x, hx⟩
  -- Step 4.2: Translate `g x = 0` into equality of real numbers `(f x : ℝ) = (x : ℝ)`.
  have hRealEq : (f x : ℝ) = (x : ℝ) := by
    -- Step 4.2.1: Rewrite `g x` explicitly and cancel.
    have : (f x : ℝ) - (x : ℝ) = 0 := by simpa [g] using hx
    exact sub_eq_zero.mp this
  -- Step 4.3: Upgrade the equality of real numbers to equality inside the subtype `I`.
  have hSubtypeEq : f x = x := by
    -- Step 4.3.1: Two elements of `I` are equal when their real parts agree.
    apply Subtype.ext
    simpa using hRealEq
  -- Step 5: Package the constructed fixed point.
  exact ⟨x, hSubtypeEq⟩
