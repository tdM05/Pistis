import Mathlib

open Filter Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators


/-Informal Statement

Suppose $V$ is a real vector space and $T \in \mathcal{L}(V)$ has no eigenvalues. Prove that every subspace of $V$ invariant under $T$ has even dimension.
-/

/-Informal Proof

First off, let us assume that $U$ is a subspace of $V$ that is invariant under $T$. Therefore, $\left.T\right|_U \in \mathcal{L}(U)$. If $\operatorname{dim}$ $U$ were odd, then $\left.T\right|_U$ would have an eigenvalue $\lambda \in \mathbb{R}$, so there would exist a nonzero vector $u \in U$ such that
$$
\left.T\right|_U u=\lambda u .
$$
So, this would imply that $T_u=\lambda u$, which would imply that $\lambda$ is an eigenvalue of $T$. But $T$ has no eigenvalues, so $\operatorname{dim} U$ must be even.
-/

theorem Axler_exercise_5_24 {V : Type*} [AddCommGroup V]
  [Module ℝ V] [FiniteDimensional ℝ V] {T : End ℝ V}
  (hT : ∀ c : ℝ, eigenspace T c = ⊥) {U : Submodule ℝ V}
  (hU : Submodule.map T U = U) : Even (finrank ℝ U) := by
  classical
  -- Step 0: make the base field explicit in the goal.

  /-
  Step-by-step helper: a monic real polynomial of odd degree has a real root.
  We use this for the characteristic polynomial of the restricted map.
  -/
  have monic_odd_real_root :
      ∀ p : ℝ[X], p.Monic → Odd p.natDegree → ∃ x : ℝ, p.eval x = 0 := by
    intro p hmonic hodd
    -- Step 1: establish that the degree of `p` is positive.
    -- Step 1.1: `p` is nonzero because it is monic.
    have hp_ne : p ≠ 0 := hmonic.ne_zero
    -- Step 1.2: translate the oddness of `natDegree` into a positive degree statement.
    have hp_deg_pos : 0 < p.degree := by
      -- `hodd.pos` gives `0 < p.natDegree`; cast to `WithBot ℕ` and rewrite degree.
      have hnat : 0 < p.natDegree := hodd.pos
      have hwb : (0 : WithBot ℕ) < (p.natDegree : WithBot ℕ) := by exact_mod_cast hnat
      simpa [degree_eq_natDegree hp_ne] using hwb
    -- Step 1.3: leading coefficient is `1`, hence nonnegative.
    have hp_lead_nonneg : 0 ≤ p.leadingCoeff := by
      simp [hmonic.leadingCoeff]

    -- Step 2: behavior of `p` at `+∞` -- it tends to `+∞` since leading coeff ≥ 0 and degree > 0.
    have hp_tendsto_pos :
        Tendsto (fun x : ℝ => p.eval x) atTop atTop :=
      (Polynomial.tendsto_atTop_iff_leadingCoeff_nonneg (P := p)).2
        ⟨hp_deg_pos, hp_lead_nonneg⟩

    -- Step 3: analyze the reflected polynomial `q(x) = p(-x)` to control the value at `-∞`.
    let q : ℝ[X] := p.comp (-X)

    -- Step 3.1: evaluate `q` explicitly.
    have hq_eval : ∀ x : ℝ, q.eval x = p.eval (-x) := by
      intro x
      -- `eval_comp` gives `eval x (p.comp (-X)) = eval (-x) p`.
      simp [q, Polynomial.eval_comp]

    -- Step 3.2: compute the degree of `q`; it matches the degree of `p`.
    have hq_nat : q.natDegree = p.natDegree := by
      -- `natDegree_comp` with `natDegree (-X) = 1`.
      have := Polynomial.natDegree_comp (p := p) (q := (-X : ℝ[X]))
      -- simplify the right-hand side using `natDegree_neg` and `natDegree_X`.
      simpa [q] using this
    have hq_deg_pos : 0 < q.degree := by
      -- rewrite the degree using `hq_nat`.
      have hq_nat_pos : 0 < q.natDegree := by simpa [hq_nat] using hodd.pos
      exact (natDegree_pos_iff_degree_pos).1 hq_nat_pos

    -- Step 3.3: compute the leading coefficient of `q`.
    have hq_lead :
        q.leadingCoeff = (-1 : ℝ) ^ p.natDegree := by
      have hcomp := Polynomial.comp_neg_X_leadingCoeff_eq (p := p)
      -- simplify using `q` and the fact that `p` is monic.
      simp [q, hmonic.leadingCoeff, mul_comm]

    -- Step 3.4: the exponent is odd, so this leading coefficient is negative.
    have hq_lead_nonpos : q.leadingCoeff ≤ 0 := by
      have hpow : (-1 : ℝ) ^ p.natDegree = -1 := by simpa using hodd.neg_one_pow
      -- substitute the power computation into the leading coefficient.
      have hq_lead' : q.leadingCoeff = -1 := by simpa [hq_lead] using hpow
      -- conclude it is ≤ 0.
      linarith

    -- Step 3.5: `q` tends to `-∞` at `+∞`, hence `p` tends to `-∞` at `-∞`.
    have hq_tendsto_neg :
        Tendsto (fun x : ℝ => q.eval x) atTop atBot :=
      (Polynomial.tendsto_atBot_iff_leadingCoeff_nonpos (P := q)).2
        ⟨hq_deg_pos, hq_lead_nonpos⟩

    -- Step 4: pick explicit points with opposite signs using the two limits.
    -- Step 4.1: choose `Rpos` so that `p.eval x ≥ 1` for all `x ≥ Rpos`.
    obtain ⟨Rpos, hRpos⟩ :=
      (eventually_atTop.1 ((tendsto_atTop.1 hp_tendsto_pos) 1))
    -- Step 4.2: choose `Rneg` so that `q.eval x ≤ -1` (equivalently `p.eval (-x) ≤ -1`) for all `x ≥ Rneg`.
    obtain ⟨Rneg, hRneg⟩ :=
      (eventually_atTop.1 ((tendsto_atBot.1 hq_tendsto_neg) (-1)))
    -- Step 4.3: take a common bound `R`.
    let R : ℝ := max Rpos Rneg

    -- Step 4.4: record the sign information at `R` and `-R`.
    have hp_pos_R : 0 ≤ p.eval R := by
      have hge : 1 ≤ p.eval R := hRpos _ (by exact le_max_left _ _)
      linarith
    have hp_neg_R : p.eval (-R) ≤ 0 := by
      -- translate the bound for `q` using `hq_eval`.
      have hq_bound : q.eval R ≤ -1 := hRneg _ (by exact le_max_right _ _)
      have hswap : p.eval (-R) = q.eval R := (hq_eval R).symm
      linarith

    -- Step 5: apply the intermediate value theorem on the interval `[-R, R]`.
    have hcont : Continuous fun x : ℝ => p.eval x := by simpa using p.continuous
    obtain ⟨x0, hx0⟩ :=
      intermediate_value_univ₂ (a := -R) (b := R)
        (f := fun x : ℝ => p.eval x) (g := fun _ : ℝ => (0 : ℝ))
        hcont continuous_const hp_neg_R hp_pos_R
    -- Step 6: conclude `p.eval x0 = 0`, i.e., `x0` is the desired real root.
    exact ⟨x0, hx0⟩

  /-
  Now prove the main statement.
  -/

  -- Step 1: show that `U` is invariant pointwise, so we can restrict `T`.
  have hTU : ∀ x : U, T x ∈ U := by
    intro x
    -- `x` comes from `U`; `T x` belongs to `map T U`, which equals `U` by hypothesis.
    have hx_in_map : T (x : V) ∈ Submodule.map T U := by
      refine ⟨x, x.property, rfl⟩
    simpa [hU] using hx_in_map

  -- Step 2: define the restricted endomorphism on `U`.
  let T_U : End ℝ U := LinearMap.codRestrict U (T.domRestrict U) hTU

  -- Step 3: the restriction inherits the "no eigenvalues" property.
  have h_no_eig_TU : ∀ c : ℝ, eigenspace T_U c = ⊥ := by
    intro c
    -- Step 3.1: prove the inclusion `eigenspace T_U c ≤ ⊥`.
    have hle : eigenspace T_U c ≤ (⊥ : Submodule ℝ U) := by
      intro x hx
      -- Unpack `hx` to the defining equation of an eigenvector of `T_U`.
      have hx_eq : T_U x = c • x := (mem_eigenspace_iff).1 hx
      -- Drop the subtype to view it inside `V`.
      have hx_eq_V : T (x : V) = c • (x : V) := congrArg Subtype.val hx_eq
      -- Use the hypothesis on `T` to show the vector is zero in `V`.
      have hx_in_T : (x : V) ∈ eigenspace T c :=
        (mem_eigenspace_iff).2 hx_eq_V
      have hx_zero_V : (x : V) ∈ (⊥ : Submodule ℝ V) := by
        simpa [hT c] using hx_in_T
      -- Transport zero back to the subtype.
      have hx_zero : x = 0 := Subtype.ext (by simpa using hx_zero_V)
      simp [hx_zero]
    -- Step 3.2: combine with the trivial inclusion `⊥ ≤ eigenspace`.
    exact le_antisymm hle bot_le

  -- Step 4: argue by contradiction—assume the dimension of `U` is odd.
  by_contra h_even
  -- Extract the oddness from the negated evenness.
  have h_even_r : ¬ Even (finrank ℝ U) := by simpa using h_even
  have h_odd : Odd (finrank ℝ U) := by
    -- Step 4.1: split the parity and discard the impossible even case.
    rcases Nat.even_or_odd (finrank ℝ U) with h_even' | h_odd'
    · exact (False.elim (h_even_r h_even'))
    · exact h_odd'

  -- Step 5: apply the polynomial lemma to the characteristic polynomial of `T_U`.
  have hchar_monic : (T_U.charpoly).Monic := LinearMap.charpoly_monic T_U
  have hchar_nat :
      T_U.charpoly.natDegree = finrank ℝ U := LinearMap.charpoly_natDegree (f := T_U)
  have hchar_odd : Odd T_U.charpoly.natDegree := by
    -- rewrite using the previous equality.
    simpa [hchar_nat] using h_odd
  obtain ⟨μ, hμ_root⟩ :=
    monic_odd_real_root (T_U.charpoly) hchar_monic hchar_odd

  -- Step 6: a real root of the characteristic polynomial yields an eigenvalue.
  have hμ_isRoot : (T_U.charpoly).IsRoot μ := by
    -- `IsRoot` is the same as `eval μ = 0`.
    simpa [Polynomial.IsRoot] using hμ_root
  have hμ_eig : T_U.HasEigenvalue μ :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly (f := T_U) μ).2 hμ_isRoot

  -- Step 7: derive the final contradiction with the "no eigenvalues" property.
  obtain ⟨v, hv_vec⟩ := hμ_eig.exists_hasEigenvector
  have hv_pair : v ∈ eigenspace T_U μ ∧ v ≠ 0 := (hasEigenvector_iff).1 hv_vec
  have hv_mem : v ∈ eigenspace T_U μ := hv_pair.1
  have hv_ne : v ≠ 0 := hv_pair.2
  have hv_zero : v = 0 := by
    -- The eigenspace is trivial by `h_no_eig_TU`.
    have hv_bot : v ∈ (⊥ : Submodule ℝ U) := by
      simpa [h_no_eig_TU μ] using hv_mem
    simpa using hv_bot
  -- Contradiction: we produced a nonzero eigenvector that must be zero.
  exact hv_ne hv_zero


/-
The original formalization uses `Submodule.map T U = U` (i.e., T(U) = U) to encode
"U is invariant under T." The standard mathematical definition of invariance is
T(U) ⊆ U, which in Lean is `Submodule.map T U ≤ U`.

While the two are logically EQUIVALENT under the hypothesis that T has no
eigenvalues (no eigenvalues ⟹ 0 is not an eigenvalue ⟹ T is injective ⟹
T|_U is injective ⟹ T|_U is surjective in finite dimensions ⟹ T(U) = U),
the `≤` formulation is a more literal translation of the informal statement because:

  1. It directly mirrors the standard definition of "invariant subspace."
  2. The equivalence with `= U` is a non-trivial consequence of the other
     hypotheses, not something the reader of the informal statement is expected
     to silently assume.
  3. A formalization should encode what the statement SAYS, not a simplified
     equivalent that requires reasoning to see is the same.
-/
theorem Axler_exercise_5_24_more_literal {V : Type*} [AddCommGroup V]
  [Module ℝ V] [FiniteDimensional ℝ V] {T : End ℝ V}
  (hT : ∀ c : ℝ, eigenspace T c = ⊥) {U : Submodule ℝ V}
  (hU : Submodule.map T U ≤ U) : Even (finrank ℝ U) := by
  -- Strategy: reduce to the original theorem `Axler_exercise_5_24` by upgrading
  -- the hypothesis `Submodule.map T U ≤ U` to `Submodule.map T U = U`.
  -- Under "T has no eigenvalues", T is injective ⟹ T|_U injective ⟹
  -- T|_U surjective (finite-dimensional) ⟹ T(U) = U.

  -- Step 1: Show T is injective.
  -- Step 1.1: eigenspace T 0 = ker T (since T - 0•id = T, so their kernels coincide).
  have hker_eq : LinearMap.ker T = eigenspace T 0 := by
    ext x; rw [LinearMap.mem_ker, mem_eigenspace_iff, zero_smul]
  -- Step 1.2: By hypothesis hT, eigenspace T 0 = ⊥. Combined with Step 1.1, ker T = ⊥.
  have hker : LinearMap.ker T = ⊥ := by rw [hker_eq]; exact hT 0
  -- Step 1.3: ker T = ⊥ is equivalent to T being injective.
  have hT_inj : Function.Injective T := LinearMap.ker_eq_bot.mp hker

  -- Step 2: Prove `Submodule.map T U = U` (upgrade from ≤ to =).
  have hU_eq : Submodule.map T U = U := by
    -- Step 2.1: The ≤ direction is our hypothesis hU. We prove the ≥ direction.
    apply le_antisymm hU
    -- Step 2.2: Define T restricted to U as a linear map U → U.
    -- For every x ∈ U, T x ∈ U (by hU: T(U) ⊆ U).
    have hTU : ∀ x : U, T (x : V) ∈ U := fun x => hU ⟨x, x.property, rfl⟩
    let T_U : U →ₗ[ℝ] U := LinearMap.codRestrict U (T.domRestrict U) hTU
    -- Step 2.3: T_U is injective (inherited from T's injectivity on V).
    -- If T_U x = T_U y, then T x = T y (as elements of V), so x = y by hT_inj.
    have hT_U_inj : Function.Injective T_U := by
      intro x y hxy
      have hval : (T_U x : V) = (T_U y : V) := congrArg Subtype.val hxy
      exact Subtype.ext (hT_inj hval)
    -- Step 2.4: An injective endomorphism of a finite-dimensional space is surjective.
    -- U is finite-dimensional (as a submodule of finite-dimensional V).
    have hT_U_surj : Function.Surjective T_U :=
      LinearMap.surjective_of_injective hT_U_inj
    -- Step 2.5: Surjectivity of T_U means every u ∈ U is in the image T(U).
    -- For any u ∈ U, there exists v ∈ U with T v = u, so u ∈ Submodule.map T U.
    intro u hu
    obtain ⟨v, hv⟩ := hT_U_surj ⟨u, hu⟩
    exact ⟨v, v.property, congrArg Subtype.val hv⟩

  -- Step 3: Apply the original theorem with the upgraded hypothesis.
  exact Axler_exercise_5_24 hT hU_eq
