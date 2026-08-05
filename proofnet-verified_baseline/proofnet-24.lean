import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators ENNReal ComplexConjugate



/-Informal Statement

Suppose $U$ is a subspace of $V$. Prove that $U^{\perp}=\{0\}$ if and only if $U=V$
-/

/-Informal Proof

$V=U \bigoplus U^{\perp}$, therefore $U^\perp = \{0\}$ iff $U=V$.
-/

theorem Axler_exercise_6_16 {K V : Type*} [RCLike K] [NormedAddCommGroup V] [InnerProductSpace K V]
  {U : Submodule K V} :
  U.orthogonal = ⊥  ↔ U = ⊤ := by
  sorry

-- NOTE: The naive statement `Uᗮ = ⊥ ↔ U = ⊤` is not valid without additional
-- hypotheses (e.g. closedness of `U`).  See `Axler_exercise_6_16_neg` for an explicit
-- counterexample and `Axler_exercise_6_16_corrected` for a corrected formulation.

/-
Step-by-step diagnosis:
- Step A: The claim as stated fails because `Uᗮ = ⊥` only forces the *closure* of `U` to be all of
  `V`. Without a closedness (or orthogonal projection) assumption, a dense proper subspace produces
  a counterexample.
- Step B: We will show this explicitly inside `ℓ²(ℕ, ℝ)` by taking the span of standard basis
  vectors (finite-support sequences). This subspace is dense, its orthogonal complement is `⊥`,
  yet it is strictly smaller than `ℓ²(ℕ, ℝ)`.
--/
theorem Axler_exercise_6_16_neg : ¬ (∀ (K V : Type*) [RCLike K] [NormedAddCommGroup V] [InnerProductSpace K V]
  (U : Submodule K V), U.orthogonal = ⊥ ↔ U = ⊤) := by
  -- Step 1: Assume the universally quantified false statement.
  intro h
  -- Step 2: Work in universe-lifted copies of `ℝ` and `ℓ²(ℕ, ℝ)`.
  -- The lift is necessary because the theorem quantifies over arbitrary universe levels.
  -- In particular, the hypothesis has `K : Type u₁` and `V : Type u₂`, so specializing it
  -- directly to the concrete `ℝ : Type 0` can fail when Lean has already fixed `u₁`.
  -- `ULift` presents the same mathematical counterexample at the universe levels demanded by `h`.
  let K := ULift ℝ
  let V0 := ↥(lp (fun _ : ℕ => ℝ) 2)
  let V := ULift V0
  -- Step 2.1: Transfer the normed field structure from `ℝ` to its universe lift.
  letI : NormedField K :=
    NormedField.induced K ℝ (ULift.ringEquiv : K ≃+* ℝ) ULift.down_injective
  letI : DenselyNormedField K := {
    lt_norm_lt := by
      intro x y hx hxy
      obtain ⟨a, ha1, ha2⟩ := DenselyNormedField.lt_norm_lt (α := ℝ) x y hx hxy
      exact ⟨ULift.up a, by simpa, by simpa⟩ }
  -- Step 2.2: The lifted real field is still `RCLike`; all operations are transported by `down`.
  letI : StarRing K := starRingOfComm
  letI : RCLike K := {
    re := (ULift.ringEquiv : K ≃+* ℝ).toAddMonoidHom
    im := 0
    I := 0
    I_re_ax := by rfl
    I_mul_I_ax := Or.inl rfl
    re_add_im_ax := by
      intro z
      ext
      change z.down + 0 * 0 = z.down
      ring
    ofReal_re_ax := by intro r; rfl
    ofReal_im_ax := by intro r; simp
    mul_re_ax := by
      intro z w
      change z.down * w.down = z.down * w.down - 0 * 0
      ring
    mul_im_ax := by intro z w; simp
    conj_re_ax := by
      intro z
      change (star z).down = z.down
      rfl
    conj_im_ax := by intro z; simp
    conj_I_ax := by simp
    norm_sq_eq_def_ax := by
      intro z
      change ‖z.down‖ ^ 2 = z.down * z.down + 0 * 0
      rw [Real.norm_eq_abs]
      nlinarith [sq_abs z.down]
    mul_im_I_ax := by intro z; simp
    le_iff_re_im := by
      intro z w
      change z.down ≤ w.down ↔ z.down ≤ w.down ∧ 0 = 0
      simp }
  -- Step 2.3: Transfer the real inner product on `ℓ²` to the lifted vector space.
  letI : NormedSpace K V := {
    norm_smul_le := by
      intro c x
      change ‖c.down • x.down‖ ≤ ‖c.down‖ * ‖x.down‖
      exact norm_smul_le c.down x.down }
  letI : Inner K V := ⟨fun x y => ULift.up (inner ℝ x.down y.down)⟩
  letI : InnerProductSpace K V := {
    norm_sq_eq_re_inner := by
      intro x
      change ‖x.down‖ ^ 2 = inner ℝ x.down x.down
      simp
    conj_inner_symm := by
      intro x y
      ext
      change inner ℝ y.down x.down = inner ℝ x.down y.down
      simpa using (inner_conj_symm (𝕜 := ℝ) x.down y.down)
    add_left := by
      intro x y z
      ext
      change inner ℝ (x.down + y.down) z.down =
        inner ℝ x.down z.down + inner ℝ y.down z.down
      simp [inner_add_left]
    smul_left := by
      intro x y r
      ext
      change inner ℝ (r.down • x.down) y.down = r.down * inner ℝ x.down y.down
      simp [inner_smul_left] }
  -- Step 3: Let `U` be the span of the coordinate basis vectors in the lifted `ℓ²`.
  let e : ℕ → V := fun n => ULift.up (lp.single 2 n (1 : ℝ))
  let U : Submodule K V := Submodule.span K (Set.range e)
  have hEquiv : U.orthogonal = ⊥ ↔ U = ⊤ := h K V U
  -- Step 4: Prove `Uᗮ = ⊥`. A vector orthogonal to every basis vector has every coordinate zero.
  have hOrthBot : U.orthogonal = (⊥ : Submodule K V) := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_orthogonal] at hv
    have hCoord : ∀ n : ℕ, (v.down : ℕ → ℝ) n = 0 := by
      intro n
      have hmem : e n ∈ U := Submodule.subset_span ⟨n, rfl⟩
      have h0K := hv (e n) hmem
      have h0R : inner ℝ (lp.single 2 n (1 : ℝ) : V0) v.down = 0 := by
        exact congrArg ULift.down h0K
      simpa [lp.inner_single_left] using h0R
    apply ULift.ext
    exact lp.ext (funext fun n => by simpa using hCoord n)
  -- Step 5: Prove `U ≠ ⊤` using the non-finitely-supported vector `((1 / 2)^n)_n`.
  have hUneTop : U ≠ ⊤ := by
    -- Step 5.1: The geometric sequence belongs to `ℓ²`.
    have hf_mem : Memℓp (fun n : ℕ => (1 / 2 : ℝ) ^ n) 2 := by
      apply memℓp_gen
      have htoReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num
      rw [htoReal]
      have hsum : Summable (fun n : ℕ => ((1 / 2 : ℝ) ^ n) ^ 2) := by
        have hgeom : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
          summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
            (by norm_num : (1 / 4 : ℝ) < 1)
        convert hgeom using 1
        ext n
        calc
          ((1 / 2 : ℝ) ^ n) ^ 2 = (1 / 2 : ℝ) ^ (n * 2) := by rw [pow_mul]
          _ = (1 / 2 : ℝ) ^ (2 * n) := by rw [Nat.mul_comm]
          _ = ((1 / 2 : ℝ) ^ 2) ^ n := by rw [pow_mul]
          _ = (1 / 4 : ℝ) ^ n := by norm_num
      simpa [Real.norm_eq_abs, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hsum
    -- Step 5.2: Lift the sequence into `V`, and record that no coordinate is zero.
    set x0 : V0 := ⟨fun n => (1 / 2 : ℝ) ^ n, hf_mem⟩ with hx0def
    set x : V := ULift.up x0 with hxdef
    have hx_apply : ∀ n : ℕ, (x.down : ℕ → ℝ) n = (1 / 2 : ℝ) ^ n := fun _ => rfl
    have hx_ne : ∀ n : ℕ, (x.down : ℕ → ℝ) n ≠ 0 := fun n => by
      rw [hx_apply]; exact pow_ne_zero _ (by norm_num)
    -- Step 5.3: If `U = ⊤`, then `x` is a finite linear combination of basis vectors.
    intro hTop
    have hx_in_U : x ∈ U := by rw [hTop]; trivial
    change x ∈ Submodule.span K (Set.range e) at hx_in_U
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hx_in_U
    obtain ⟨c, hc⟩ := hx_in_U
    -- Step 5.4: Pick a coordinate outside the finite support of that linear combination.
    obtain ⟨n, hn⟩ : ∃ n, n ∉ c.support :=
      ⟨c.support.sup (fun k => k) + 1, fun hmem =>
        Nat.not_succ_le_self _ (Finset.le_sup (f := fun k => k) hmem)⟩
    -- Step 5.5: Coordinate evaluation of one basis term.
    have hsingle (a : K) (i m : ℕ) :
        (((a • e i : V).down : V0) : ℕ → ℝ) m =
          a.down * ((Pi.single i (1 : ℝ) : ℕ → ℝ) m) := by
      change (((a.down • (lp.single 2 i (1 : ℝ) : V0) : V0) : ℕ → ℝ) m) =
        a.down * ((Pi.single i (1 : ℝ) : ℕ → ℝ) m)
      simp [lp.coeFn_smul, lp.coeFn_single, Pi.smul_apply, smul_eq_mul]
    -- Step 5.6: Coordinate evaluation commutes with finite sums.
    have hAdd (y z : V) (m : ℕ) :
        (((y + z).down : V0) : ℕ → ℝ) m =
          ((y.down : V0) : ℕ → ℝ) m + ((z.down : V0) : ℕ → ℝ) m := by
      rfl
    have hsumCoord (s : Finset ℕ) (d : ℕ → K) (m : ℕ) :
        (((∑ i ∈ s, d i • e i : V).down : V0) : ℕ → ℝ) m =
          ∑ i ∈ s, (d i).down * ((Pi.single i (1 : ℝ) : ℕ → ℝ) m) := by
      classical
      induction s using Finset.induction_on with
      | empty =>
          simp
      | insert i s his ih =>
          rw [Finset.sum_insert his, Finset.sum_insert his]
          rw [hAdd, hsingle, ih]
    -- Step 5.7: At coordinate `n`, every finite-sum term vanishes because `n ∉ c.support`.
    have hLHS : (((c.sum fun i a => a • e i : V).down : V0) : ℕ → ℝ) n = 0 := by
      classical
      have hcoe : (((c.sum fun i a => a • e i : V).down : V0) : ℕ → ℝ) n
          = c.sum (fun i a => a.down * ((Pi.single i (1 : ℝ) : ℕ → ℝ) n)) := by
        simpa [Finsupp.sum] using hsumCoord c.support (fun i => c i) n
      rw [hcoe]
      change ∑ i ∈ c.support, (c i).down * ((Pi.single i (1 : ℝ) : ℕ → ℝ) n) = 0
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hin : i = n
      · subst hin; exact absurd hi hn
      · have hni : n ≠ i := fun hni => hin hni.symm
        simp [Pi.single, Function.update, hni]
    -- Step 5.8: But the same coordinate is `(1 / 2)^n`, which is nonzero.
    have hRHS : (((c.sum fun i a => a • e i : V).down : V0) : ℕ → ℝ) n =
        (1 / 2 : ℝ) ^ n := by
      exact (congrArg (fun y : V => (((y.down : V0) : ℕ → ℝ) n)) hc).trans (hx_apply n)
    exact (hx_ne n) (hRHS.symm.trans hLHS)
  -- Step 6: The assumed equivalence now forces the proper submodule `U` to be top.
  exact hUneTop (hEquiv.mp hOrthBot)


/-
The original statement is correct, but as a mathematical claim it’s false in general for inner
product spaces. The informal proof line “V = U ⊕ Uᗮ” only holds when U is closed and the ambient
space is complete (or when V is finite-dimensional, in which case every subspace is closed).
Without these hypotheses one can have a proper dense subspace U with Uᗮ = {0} but U ≠ V.

Fix: require both `(hU : IsClosed (U : Set V))` and `[CompleteSpace V]`, which is weaker than assuming `[FiniteDimensional K V]` or `[U.HasOrthogonalProjection]`.
--/
theorem Axler_exercise_6_16_corrected {K V : Type*} [RCLike K] [NormedAddCommGroup V]
  [InnerProductSpace K V] [CompleteSpace V] {U : Submodule K V}
  (hU : IsClosed (U : Set V)) :
  U.orthogonal = ⊥ ↔ U = ⊤ := by
  classical
  constructor
  · -- Step 1: Assume that the orthogonal complement is trivial and deduce that `U` equals `⊤`.
    intro hOrth
    -- Step 1.1: A closed submodule has dense span precisely when its orthogonal complement vanishes.
    have hClosureTop : U.topologicalClosure = (⊤ : Submodule K V) :=
      (Submodule.topologicalClosure_eq_top_iff).2 hOrth
    -- Step 1.2: Invoke the closedness hypothesis and eliminate the topological closure.
    have hClosedEq : U.topologicalClosure = U := hU.submodule_topologicalClosure_eq
    simpa [hClosedEq] using hClosureTop
  · -- Step 2: Conversely, if `U = ⊤`, its orthogonal complement is clearly `⊥`.
    intro hTop
    simp [hTop]
