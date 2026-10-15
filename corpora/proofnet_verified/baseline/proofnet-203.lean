import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators


/-Informal Statement

Suppose $S, T \in \mathcal{L}(V)$. Prove that $S T$ and $T S$ have the same eigenvalues.
-/

/-Informal Proof

To start, let $\lambda \in F$ be an eigenvalue of $S T$. Now, we would want $\lambda$ to be an eigenvalue of $T S$. Since $\lambda$, by itself, is an eigenvalue of $S T$, then there has to be a nonzero vector $v \in V$ such that $(S T) v=\lambda v$.
Now, With a given reference that $(S T) v=\lambda v$, you will then have the following: $(T S)(T v)=$ $T(S T v)=T(\lambda v)=\lambda T v$
If $T v \neq 0$, then the listed equation above shows that $\lambda$ is an eigenvalue of $T S$.
If $T v=0$, then $\lambda=0$, since $S(T v)=\lambda T v$. This also means that $T$ isn't invertible, which would imply that $T S$ isn't invertible, which can also be implied that $\lambda$, which equals 0 , is an eigenvalue of $T S$.
Step 3
3 of 3
Now, regardless of whether $T v=0$ or not, we would have shown that $\lambda$ is an eigenvalue of $T S$. Since $\lambda$ (was) an arbitrary eigenvalue of $S T$, we have shown that every single eigenvalue of $S T$ is an eigenvalue of $T S$. When you do reverse the roles of both $S$ and $T$, then we can conclude that that every single eigenvalue of $T S$ is also an eigenvalue of $S T$. Therefore, both $S T$ and $T S$ have the exact same eigenvalues.
-/

theorem Axler_exercise_5_11 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] (S T : End F V) :
  (S * T).Eigenvalues = (T * S).Eigenvalues := by
  sorry

/-
Explanation (why the original formal statement is false as written):

*Missing premise*: The claim fails on infinite‑dimensional spaces.  For
  linear maps `S, T : V →ₗ[F] V`, the nonzero eigenvalues of `S*T` and
  `T*S` coincide, but the value `0` can appear for one composition and
  not the other.  A classical counterexample uses shift operators on an
  infinite basis; `S*T` becomes the identity (no zero eigenvalue) while
  `T*S` kills one basis vector (zero IS an eigenvalue).  Therefore the
  equality of eigenvalue types is wrong without a finite‑dimensional
  hypothesis.
-/

/-!
### Concrete counterexample (disproves the original statement)

We work on the space of sequences `ℕ → F`.  Define:
* `shiftRight`  : inserts a zero at the front (moves every entry one step to the right);
* `shiftLeft`   : drops the first entry (moves every entry one step to the left).

Then `shiftLeft * shiftRight = 1`, while `shiftRight * shiftLeft` is the
projection that zeroes out the first coordinate.  Hence `0` is an
eigenvalue of `shiftRight * shiftLeft` (witnessed by the sequence
`δ₀ = (1,0,0,…)`), but `0` is *not* an eigenvalue of the identity map.
-/

section Counterexample_exercise_5_11

open scoped BigOperators

variable (F : Type*) [Field F]

-- Step 1: Define the right-shift operator `T`, sending `f` to the sequence with a leading zero.
def shiftRight : (ℕ → F) →ₗ[F] (ℕ → F) :=
{ toFun := fun f n => match n with
    | 0      => 0
    | Nat.succ k => f k,
  map_add' := by
    intro f g; funext n; cases n <;> simp,
  map_smul' := by
    intro a f; funext n; cases n <;> simp }

-- Step 2: Define the left-shift operator `S`, sending `f` to the tail of the sequence.
def shiftLeft : (ℕ → F) →ₗ[F] (ℕ → F) :=
{ toFun := fun f n => f (Nat.succ n),
  map_add' := by
    intro f g; funext n; simp,
  map_smul' := by
    intro a f; funext n; simp }

-- Step 3: Define the projection that kills only the first coordinate.
def dropFirst : (ℕ → F) →ₗ[F] (ℕ → F) :=
{ toFun := fun f n => if n = 0 then 0 else f n,
  map_add' := by
    intro f g; funext n; by_cases h : n = 0 <;> simp [h],
  map_smul' := by
    intro a f; funext n; by_cases h : n = 0 <;> simp [h] }

-- Step 4: The compositions behave as described: `S ∘ T = id`, `T ∘ S = dropFirst`.
lemma shiftLeft_mul_shiftRight :
    shiftLeft F * shiftRight F = (1 : End F (ℕ → F)) := by
  -- Step 4.1: Extensionality reduces equality of linear maps to pointwise equality.
  ext f n; cases n <;> simp [shiftLeft, shiftRight]

lemma shiftRight_mul_shiftLeft :
    shiftRight F * shiftLeft F = dropFirst F := by
  -- Step 4.2: Compute the composition on each coordinate; the first one becomes zero.
  ext f n; cases n <;> simp [shiftLeft, shiftRight, dropFirst]

-- Step 5: A convenient nonzero vector supported at 0.
def delta0 : ℕ → F := fun n => if n = 0 then 1 else 0

lemma delta0_ne_zero : delta0 F ≠ (0 : ℕ → F) := by
  -- Step 5.1: Evaluate at index 0 to show the function is not identically zero.
  intro h
  have h0 : (delta0 F) 0 = 0 := by simpa using congrArg (fun g => g 0) h
  simp [delta0] at h0

-- Step 6: `delta0` is a 0‑eigenvector for the projection `dropFirst`.
lemma dropFirst_hasEigenvector_zero :
    HasEigenvector (dropFirst F) 0 (delta0 F) := by
  -- Step 6.1: Show the image is zero, i.e. it satisfies the eigenvalue equation with μ = 0.
  have h_img : dropFirst F (delta0 F) = 0 := by
    funext n
    by_cases h : n = 0
    · simp [dropFirst, h]
    · simp [dropFirst, delta0, h]
  -- Step 6.2: Translate the equality into eigenspace membership.
  have h_mem : delta0 F ∈ eigenspace (dropFirst F) 0 := by
    simp [h_img]
  -- Step 6.3: Package membership and nonzeroness into `HasEigenvector`.
  exact ⟨h_mem, delta0_ne_zero F⟩

-- Step 7: Therefore `0` is an eigenvalue of `dropFirst`.
lemma dropFirst_hasEigenvalue_zero :
    HasEigenvalue (dropFirst F) 0 :=
  Module.End.hasEigenvalue_of_hasEigenvector
    (f := dropFirst F) (μ := 0) (x := delta0 F)
    (dropFirst_hasEigenvector_zero (F := F))

-- Step 7.1: The projection `dropFirst` also has `1` as an eigenvalue.
lemma dropFirst_hasEigenvalue_one :
    HasEigenvalue (dropFirst F) 1 := by
  classical
  -- Step 7.1.1: Choose a vector whose first coordinate is zero and all others are `1`.
  let v : ℕ → F := fun n => if n = 0 then 0 else 1
  -- Step 7.1.2: Show that this vector is nonzero (its value at `1` is `1`).
  have hv_ne : v ≠ 0 := by
    intro h
    have h1 : v 1 = 0 := by
      simpa using congrArg (fun g => g 1) h
    -- But by construction, `v 1 = 1`.
    simp [v] at h1
  -- Step 7.1.3: Show that `v` is a `1`‑eigenvector of `dropFirst`.
  have hv_eig : HasEigenvector (dropFirst F) 1 v := by
    -- First show the defining equation `dropFirst v = 1 • v = v`.
    have h_eq : (dropFirst F) v = (1 : F) • v := by
      funext n
      by_cases h0 : n = 0
      · -- At coordinate `0`, both sides are `0`.
        subst h0
        simp [dropFirst, v]
      · -- At coordinates `n ≠ 0`, both sides evaluate to `1`.
        have : n ≠ 0 := h0
        simp [dropFirst, v, this]
    -- Package this equality and the non‑vanishing of `v` into the eigenvector predicate.
    refine And.intro ?h_mem hv_ne
    -- Membership in the eigenspace is exactly the equation `f v = μ • v`.
    exact (mem_eigenspace_iff.mpr h_eq)
  -- Step 7.1.4: A nonzero eigenvector yields an eigenvalue.
  exact Module.End.hasEigenvalue_of_hasEigenvector
    (f := dropFirst F) (μ := 1) (x := v) hv_eig

-- Step 8: The identity has no zero eigenvalue.
lemma id_has_no_zero_eigenvalue :
    ¬ HasEigenvalue (1 : End F (ℕ → F)) 0 := by
  -- Step 8.1: Direct computation shows the 0‑eigenspace of the identity is trivial.
  intro h
  -- Reinterpret the hypothesis in terms of the eigenspace description.
  change eigenspace (1 : End F (ℕ → F)) 0 ≠ (⊥ : Submodule F (ℕ → F)) at h
  -- But the kernel of the identity is the zero submodule.
  have hker : eigenspace (1 : End F (ℕ → F)) 0 = (⊥ : Submodule F (ℕ → F)) := by
    -- eigenspace at 0 is the kernel; the kernel of the identity is ⊥.
    have : LinearMap.ker (1 : End F (ℕ → F)) = (⊥ : Submodule F (ℕ → F)) := by
      ext x
      constructor <;> intro hx <;> simpa [LinearMap.mem_ker] using hx
    simpa [Module.End.eigenspace_zero] using this
  exact h hker

-- Step 8.2: Any eigenvalue of the identity must be `1`.
lemma eigenvalue_id_eq_one {μ : F} :
    HasEigenvalue (1 : End F (ℕ → F)) μ → μ = 1 := by
  classical
  -- Step 8.2.1: Extract a nonzero eigenvector corresponding to `μ`.
  intro hμ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  -- `hv` states that `v` is a nonzero eigenvector: `(1) v = μ • v` and `v ≠ 0`.
  have h_eq : (1 : End F (ℕ → F)) v = μ • v := hv.apply_eq_smul
  -- Step 8.2.2: Simplify the identity action so the equation lives in the module.
  have h_eq' : v = μ • v := by simpa using h_eq
  -- Step 8.2.3: Rearrange the equation to show `(1 - μ) • v = 0` in the module.
  have h_smul : (1 : F) • v = μ • v := by simpa using h_eq'
  have h_sub' : (1 : F) • v - μ • v = 0 := sub_eq_zero.mpr h_smul
  have h_sub : (1 - μ) • v = 0 := by
    -- Use the standard scalar–module identity `(r - s) • v = r • v - s • v`.
    simpa [sub_smul] using h_sub'
  -- Step 8.2.4: Evaluate at some coordinate where `v` is nonzero.
  have hex : ∃ n : ℕ, v n ≠ 0 := by
    -- If all coordinates were zero, then `v = 0`, contradicting `hv.2`.
    by_contra h_all
    push_neg at h_all
    have hv_zero : v = 0 := by
      funext n
      exact h_all n
    exact hv.2 hv_zero
  rcases hex with ⟨n0, hn0⟩
  -- Step 8.2.5: At the chosen coordinate, `(1 - μ) • v n0 = 0` inside the field.
  have h_coord : (1 - μ) • v n0 = 0 := by
    -- Apply the functional equality `h_sub` at coordinate `n0`.
    have := congrArg (fun w => w n0) h_sub
    -- Scalar multiplication on functions is pointwise.
    simpa using this
  -- Step 8.2.6: Use the fact that `F` has no zero smul divisors to deduce `1 - μ = 0`.
  have h_scalar : (1 - μ) = 0 := by
    -- In the module `F` over itself, the only way a nonzero vector is killed by a scalar
    -- is when that scalar is zero.
    have := (smul_eq_zero_iff_left (r := 1 - μ) (m := v n0) hn0).1
    exact this h_coord
  -- Step 8.2.7: Finally, solve for `μ` from `1 - μ = 0`.
  have h_one : (1 : F) = μ := sub_eq_zero.mp h_scalar
  exact h_one.symm

-- Step 8.3: The identity endomorphism has at most one eigenvalue.
lemma eigenvalues_id_subsingleton :
    Subsingleton (Eigenvalues (1 : End F (ℕ → F))) := by
  classical
  -- Step 8.3.1: Show any two bundled eigenvalues of the identity coincide.
  refine ⟨?_h⟩
  intro e₁ e₂
  -- Extract the scalar eigenvalues from the bundled data.
  have hμ₁ : HasEigenvalue (1 : End F (ℕ → F)) (e₁ : F) := by
    simpa [HasEigenvalue] using e₁.property
  have hμ₂ : HasEigenvalue (1 : End F (ℕ → F)) (e₂ : F) := by
    simpa [HasEigenvalue] using e₂.property
  -- Both scalars must equal `1`, hence they are equal to each other.
  have hval₁ : (e₁ : F) = 1 := eigenvalue_id_eq_one (F := F) hμ₁
  have hval₂ : (e₂ : F) = 1 := eigenvalue_id_eq_one (F := F) hμ₂
  have hvals : (e₁ : F) = (e₂ : F) := by simp [hval₁, hval₂]
  -- Equality of the underlying scalars determines equality of the bundled eigenvalues.
  exact Subtype.ext hvals

-- Step 9: Assemble the counterexample using the two compositions.
theorem exercise_5_11_counterexample :
    Eigenvalues (shiftLeft F * shiftRight F) ≠
      Eigenvalues (shiftRight F * shiftLeft F) := by
  classical
  -- Step 9.1: Pin down the two compositions: one is the identity, the other is the projection `dropFirst`.
  have h_left_id : shiftLeft F * shiftRight F = (1 : End F (ℕ → F)) :=
    shiftLeft_mul_shiftRight (F := F)
  have h_right_drop : shiftRight F * shiftLeft F = dropFirst F :=
    shiftRight_mul_shiftLeft (F := F)
  -- Step 9.2: Translate those descriptions into qualitative facts about the eigenvalue types.
  -- Step 9.2.1: The eigenvalues of the identity form a subsingleton type.
  have h_sub_left : Subsingleton (Eigenvalues (shiftLeft F * shiftRight F)) := by
    -- Transport the subsingleton structure from the identity via `h_left_id`.
    simpa [h_left_id] using eigenvalues_id_subsingleton (F := F)
  -- Step 9.2.2: On the right, there are at least two distinct eigenvalues (0 and 1),
  --             so the eigenvalue type is *not* a subsingleton.
  have h_not_sub_right : ¬ Subsingleton (Eigenvalues (shiftRight F * shiftLeft F)) := by
    -- Package the 0‑eigenvalue of `dropFirst`.
    have h0_rhs : HasEigenvalue (shiftRight F * shiftLeft F) 0 := by
      simpa [h_right_drop] using dropFirst_hasEigenvalue_zero (F := F)
    -- Package the 1‑eigenvalue of `dropFirst`.
    have h1_rhs : HasEigenvalue (shiftRight F * shiftLeft F) 1 := by
      simpa [h_right_drop] using dropFirst_hasEigenvalue_one (F := F)
    -- Turn these into bundled eigenvalues in the `Eigenvalues` type.
    let e0 : Eigenvalues (shiftRight F * shiftLeft F) :=
      ⟨0, by simpa [HasEigenvalue] using h0_rhs⟩
    let e1 : Eigenvalues (shiftRight F * shiftLeft F) :=
      ⟨1, by simpa [HasEigenvalue] using h1_rhs⟩
    -- Show that these two bundled eigenvalues are distinct.
    have h_ne : e0 ≠ e1 := by
      intro h
      -- Compare their underlying scalars in `F`.
      have hv :
          (e0 : F) =
            (e1 : F) :=
        congrArg
          (fun x : Eigenvalues (shiftRight F * shiftLeft F) => (x : F)) h
      -- But `(e0 : F) = 0` and `(e1 : F) = 1`, contradicting `0 ≠ 1`.
      have hv0 : (e0 : F) = 0 := rfl
      have hv1 : (e1 : F) = 1 := rfl
      have : (0 : F) = 1 := by
        calc
          (0 : F) = (e0 : F) := hv0.symm
          _ = (e1 : F) := hv
          _ = (1 : F) := hv1
      exact zero_ne_one this
    -- Any subsingleton type would force `e0 = e1`, contradicting `h_ne`.
    intro h_sub
    have h_eq : e0 = e1 := h_sub.elim e0 e1
    exact h_ne h_eq
  -- Step 9.3: Assume (for contradiction) that the bundled eigenvalue *types* are equal.
  intro h_eq
  -- Step 9.3.1: Transport the subsingleton structure along the assumed type equality.
  have h_sub_right : Subsingleton (Eigenvalues (shiftRight F * shiftLeft F)) := by
    simpa [h_eq] using h_sub_left
  -- Step 9.3.2: Contradiction: the right-hand eigenvalue type is both subsingleton and
  --             non-subsingleton.
  exact h_not_sub_right h_sub_right

end Counterexample_exercise_5_11

/-!
### Negation of the original universal statement

The previous construction shows that the universally quantified claim is false.
-/
theorem Axler_exercise_5_11_neg :
    ¬ (∀ (F V : Type) [AddCommGroup V] [Field F] [Module F V]
        (S T : End F V), (S * T).Eigenvalues = (T * S).Eigenvalues) := by
  classical
  --------------------------------------------------------------------------
  -- Step 1: Assume, for contradiction, the universal statement we want
  --         to negate.  Since the goal is `¬ P`, we introduce an
  --         arbitrary hypothesis `h_univ : P` and will derive a
  --         contradiction from it.
  --------------------------------------------------------------------------
  intro h_univ

  --------------------------------------------------------------------------
  -- Step 2: Specialize this universal hypothesis to the *concrete*
  --         counterexample constructed above.
  --
  --   Step 2.1: Fix the ambient algebraic data.
  --     Step 2.1.1: Take the field `F := ℚ`, the rationals.
  --     Step 2.1.2: Take the vector space `V := ℕ → ℚ`, the space of
  --                 rational sequences indexed by natural numbers.
  --
  --   Step 2.2: Fix the specific endomorphisms on this space.
  --     Step 2.2.1: Let `S := shiftLeft ℚ`, the left‑shift operator.
  --     Step 2.2.2: Let `T := shiftRight ℚ`, the right‑shift operator.
  --
  --   Step 2.3: Apply the universal claim `h_univ` to this specific
  --             tuple `(F, V, S, T)` to obtain an equality between the
  --             eigenvalue sets of the two compositions `S*T` and `T*S`.
  --------------------------------------------------------------------------
  have h_eq_specialized :
      Eigenvalues (shiftLeft (F := ℚ) * shiftRight (F := ℚ)) =
        Eigenvalues (shiftRight (F := ℚ) * shiftLeft (F := ℚ)) := by
    ----------------------------------------------------------------------
    -- Step 2.3.1: Instantiate the universal statement with
    --             `F := ℚ`, `V := ℕ → ℚ`,
    --             `S := shiftLeft ℚ`, `T := shiftRight ℚ`.
    --             Lean infers the required additive group and module
    --             structures from these choices.
    ----------------------------------------------------------------------
    have h_inst :=
      h_univ
        ℚ (ℕ → ℚ)
        (S := shiftLeft (F := ℚ))
        (T := shiftRight (F := ℚ))
    ----------------------------------------------------------------------
    -- Step 2.3.2: The instantiated equality `h_inst` already matches
    --             the goal of this sub‑proof exactly, so we can close
    --             the goal by reusing it.
    ----------------------------------------------------------------------
    simpa using h_inst

  --------------------------------------------------------------------------
  -- Step 3: Bring in the explicit counterexample established earlier.
  --
  --   Step 3.1: The theorem `exercise_5_11_counterexample` states that
  --             for *every* field `F`, the eigenvalues of
  --               `shiftLeft F * shiftRight F`
  --             and
  --               `shiftRight F * shiftLeft F`
  --             are *not* equal.  Specializing to `F = ℚ` yields the
  --             inequality below.
  --------------------------------------------------------------------------
  have h_counterexample :
      Eigenvalues (shiftLeft (F := ℚ) * shiftRight (F := ℚ)) ≠
        Eigenvalues (shiftRight (F := ℚ) * shiftLeft (F := ℚ)) :=
    exercise_5_11_counterexample (F := ℚ)

  --------------------------------------------------------------------------
  --   Step 3.2: Combine the specialized *equality* from Step 2 with the
  --             specialized *inequality* from Step 3.1.
  --
  --             Let
  --               `A := Eigenvalues (shiftLeft ℚ * shiftRight ℚ)`
  --               `B := Eigenvalues (shiftRight ℚ * shiftLeft ℚ)`.
  --             Then
  --               * `h_eq_specialized` asserts `A = B`,
  --               * `h_counterexample` asserts `A ≠ B`.
  --             Applying `h_counterexample` to `h_eq_specialized`
  --             produces a contradiction, which shows that our initial
  --             assumption `h_univ` cannot hold.
  --------------------------------------------------------------------------
  exact h_counterexample h_eq_specialized

/-
### Corrected statement (with the missing hypothesis restored)

If `V` is finite-dimensional, then `S*T` and `T*S` do have exactly the
same eigenvalues; the characteristic polynomials coincide by the
standard matrix identity `charpoly (AB) = charpoly (BA)`, and eigenvalues
are precisely the roots of the characteristic polynomial.
-/
theorem Axler_exercise_5_11_corrected {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (S T : End F V) :
    (S * T).Eigenvalues = (T * S).Eigenvalues := by
  classical
  -- Step 1: Reduce to the characteristic polynomial identity via matrices.
  have h_charpoly :
      (S * T).charpoly = (T * S).charpoly := by
    -- Step 1.1: Work in a convenient finite basis.
    let b := Module.finBasis F V
    -- Step 1.2: Compare the characteristic polynomials via matrices.
    have hmat :
        (LinearMap.toMatrix b b (S * T)).charpoly =
          (LinearMap.toMatrix b b (T * S)).charpoly := by
      calc
        (LinearMap.toMatrix b b (S * T)).charpoly
            = (LinearMap.toMatrix b b S * LinearMap.toMatrix b b T).charpoly := by
              simp [LinearMap.toMatrix_mul]
        _ = (LinearMap.toMatrix b b T * LinearMap.toMatrix b b S).charpoly :=
            Matrix.charpoly_mul_comm _ _
        _ = (LinearMap.toMatrix b b (T * S)).charpoly := by
              simp [LinearMap.toMatrix_mul]
    -- Step 1.3: Use `charpoly_toMatrix` to translate back to linear maps.
    calc
      (S * T).charpoly
          = (LinearMap.toMatrix b b (S * T)).charpoly := by
              simp [LinearMap.charpoly_toMatrix (f := S * T) (b := b)]
      _ = (LinearMap.toMatrix b b (T * S)).charpoly := hmat
      _ = (T * S).charpoly := by
              simp [LinearMap.charpoly_toMatrix (f := T * S) (b := b)]
  -- Step 2: Equate the eigenvalue predicates using the root characterization.
  have h_pred :
      (fun μ : F => (S * T).HasEigenvalue μ) =
      (fun μ : F => (T * S).HasEigenvalue μ) := by
    funext μ
    apply propext
    -- Step 2.1: Eigenvalues are exactly the roots of the characteristic polynomial.
    have hST :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly (f := S * T) (μ := μ))
    have hTS :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly (f := T * S) (μ := μ))
    -- Step 2.2: Rewrite using the characteristic-polynomial identity.
    constructor
    · intro hμ
      have hroot : (S * T).charpoly.IsRoot μ := (hST.mp hμ)
      have hroot' : (T * S).charpoly.IsRoot μ := by
        simpa [h_charpoly] using hroot
      exact hTS.mpr hroot'
    · intro hμ
      have hroot : (T * S).charpoly.IsRoot μ := (hTS.mp hμ)
      have hroot' : (S * T).charpoly.IsRoot μ := by
        simpa [h_charpoly] using hroot
      exact hST.mpr hroot'
  -- Step 3: Equality of predicates gives equality of the bundled eigenvalue subtypes.
  have h_pred_unif :
      (fun μ : F => HasUnifEigenvalue (S * T) μ 1) =
      (fun μ : F => HasUnifEigenvalue (T * S) μ 1) := by
    simpa [HasEigenvalue] using h_pred
  simp [Eigenvalues, UnifEigenvalues, h_pred_unif]
