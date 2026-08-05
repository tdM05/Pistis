import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators


noncomputable section

open Matrix

local notation "V₂" => Fin 2 → ZMod 2
local notation "NZ₂" => { v : V₂ // v ≠ (0 : V₂) }

/-!
We prepare a detailed dictionary between the six invertible `2 × 2` matrices over `ℤ₂` and the
six permutations of three objects.  The key steps are counted and explained in the comments in each
lemma so that the formal proof mirrors the informal reasoning step by step.
-/

lemma card_nonzero_vectors : Fintype.card NZ₂ = 3 := by
  classical
  change Fintype.card { v : V₂ // v ≠ (0 : V₂) } = 3
  -- Step 1: compute the total number `4` of vectors in `(Fin 2 → ZMod 2)` via the fun-card lemma.
  have hTotal : Fintype.card V₂ = 4 := by
    simp [Fintype.card_fin, ZMod.card]
  -- Step 2: the zero vector is unique, so the corresponding subtype has cardinality `1`.
  have hZero : Fintype.card { v : V₂ // v = (0 : V₂) } = 1 := by
    simp
  -- Step 3: subtract the zero vector from the full set to get the three nonzero vectors.
  simp [hTotal, Fintype.card_subtype_compl]

@[simp] lemma card_perm_nonzero : Fintype.card (Equiv.Perm NZ₂) = 6 := by
  classical
  -- Step 1: rewrite the permutation cardinality as the factorial of `|NZ₂| = 3`.
  have hCard : Fintype.card NZ₂ = 3 := card_nonzero_vectors
  have hFact : Nat.factorial 3 = 6 := by decide
  calc
    Fintype.card (Equiv.Perm NZ₂)
        = Nat.factorial (Fintype.card NZ₂) := by simp [Fintype.card_perm]
    _ = Nat.factorial 3 := by simp [hCard]
    _ = 6 := hFact

def nzEquivFin3 : NZ₂ ≃ Fin 3 :=
  Fintype.equivFinOfCardEq card_nonzero_vectors

private def permOfLinearEquiv (e : V₂ ≃ₗ[ZMod 2] V₂) : Equiv.Perm NZ₂ :=
  -- Step 1: transport the linear equivalence to a permutation of the nonzero vectors.
  { toFun := fun v => ⟨e v, by
      -- Step 1.1: injectivity of `e` ensures nonzero vectors stay nonzero.
      simpa using (e.map_ne_zero_iff).2 v.property⟩
    , invFun := fun v => ⟨e.symm v, by
      -- Step 1.2: the inverse linear equivalence has the same preservation property.
      simpa using (e.symm.map_ne_zero_iff).2 v.property⟩
    , left_inv := by
      -- Step 1.3: restricting to the subtype keeps the standard left inverse property.
      intro v; ext i; simp
    , right_inv := by
      -- Step 1.4: similarly for the right inverse direction.
      intro v; ext i; simp }

@[simp] lemma permOfLinearEquiv_apply (e : V₂ ≃ₗ[ZMod 2] V₂) (v : NZ₂) :
    (permOfLinearEquiv e v : V₂) = e v := rfl

def linearEquivAction : (V₂ ≃ₗ[ZMod 2] V₂) →* Equiv.Perm NZ₂ where
  -- Step 1: package the permutation construction into a monoid homomorphism.
  toFun := permOfLinearEquiv
  map_one' := by
    -- Step 1.1: the identity linear map induces the identity permutation.
    ext v i; simp [permOfLinearEquiv]
  map_mul' e₁ e₂ := by
    -- Step 1.2: composition of linear equivalences matches multiplication of permutations.
    ext v i; simp [permOfLinearEquiv, Function.comp]

lemma linearEquivAction_injective : Function.Injective linearEquivAction := by
  classical
  -- Step 1: suppose two linear equivalences induce the same permutation.
  intro e₁ e₂ h
  -- Step 2: compare their values on every vector by splitting into `0` and nonzero cases.
  ext v i
  by_cases hv : v = (0 : V₂)
  -- Step 2.1: both linear equivalences send `0` to `0`.
  · subst hv
    simp
  -- Step 2.2: evaluate the equality of permutations on the nonzero vector `v`.
  · have := congrArg Subtype.val (congrArg (fun f => f ⟨v, hv⟩) h)
    -- Step 2.3: erase subtype wrappers to obtain equality of the underlying coordinates.
    have := congrArg (fun w => w i) this
    simpa [linearEquivAction, permOfLinearEquiv] using this

def glLinearEquiv :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) ≃* (V₂ ≃ₗ[ZMod 2] V₂) :=
  (Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod 2)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V₂)

def glAction : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) →* Equiv.Perm NZ₂ :=
  -- Step 1: compose the matrix-to-linear-equivalence isomorphism with the permutation action.
  linearEquivAction.comp glLinearEquiv.toMonoidHom

lemma glAction_injective : Function.Injective glAction := by
  -- Step 1: composition of the injective action with the injective `MulEquiv` remains injective.
  refine linearEquivAction_injective.comp ?_
  intro A B hAB
  exact glLinearEquiv.injective hAB

lemma card_GL_two :
    Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
  classical
  -- Step 1: apply the general cardinal formula for `GL₂` over a finite field.
  have h := Matrix.card_GL_field (n := 2) (𝔽 := ZMod 2)
  -- Step 2: translate `Nat.card` into the standard `Fintype.card`.
  have h' := by
    simpa [Nat.card_eq_fintype_card] using h
  -- Step 3: explicitly compute the product `(4 - 1) * (4 - 2) = 6`.
  have : ∏ i : Fin 2, ((2 : ℕ) ^ 2 - (2 : ℕ) ^ (i : ℕ)) = 6 := by
    classical
    simp [Fin.prod_univ_two, pow_zero, pow_one]
  -- Step 4: simplify the powers of `2` and conclude `|GL₂(ℤ₂)| = 6`.
  simpa [ZMod.card, this] using h'



/-Informal Statement

Let $T$ be the group of $2\times 2$ matrices $A$ with entries in the field $\mathbb{Z}_2$ such that $\det A$ is not equal to 0. Prove that $T$ is isomorphic to $S_3$, the symmetric group of degree 3.
-/

/-Informal Proof

The order of $T$ is $2^4-2^3-2^2+2=6$; we now find those six matrices:
$$
\begin{array}{ll}
A_1=\left(\begin{array}{ll}
1 & 0 \\
0 & 1
\end{array}\right), & A_2=\left(\begin{array}{ll}
0 & 1 \\
1 & 0
\end{array}\right) \\
A_3=\left(\begin{array}{ll}
1 & 0 \\
1 & 1
\end{array}\right), & A_4=\left(\begin{array}{ll}
1 & 1 \\
0 & 1
\end{array}\right) \\
A_5=\left(\begin{array}{ll}
0 & 1 \\
1 & 1
\end{array}\right), & A_6=\left(\begin{array}{ll}
1 & 1 \\
1 & 0
\end{array}\right)
\end{array}
$$
with orders $1,2,2,2,3,3$ respectively.
Note that $S_3$ is composed of elements
$$
\text{ id, (1 2), (1 3), (2 3), (1 2 3), (1 3 2)} 
$$
with orders 1, 2, 2, 2, 3, 3 respectively. Also note that, by Problem 17 of generate $S_3$. We also have that $\left(\begin{array}{llll}1 & 3 & 2\end{array}\right)=\left(\begin{array}{llll}1 & 2 & 3\end{array}\right)\left(\begin{array}{lll}1 & 2 & 3\end{array}\right)$, that $\left(\begin{array}{lll}1 & 3\end{array}\right)=\left(\begin{array}{lll}1 & 2 & 3\end{array}\right)\left(\begin{array}{ll}1 & 2\end{array}\right)$, $\left(\begin{array}{ll}1 & 2\end{array}\right)\left(\begin{array}{lll}1 & 2 & 3\end{array}\right)=\left(\begin{array}{ll}2 & 3\end{array}\right)$ and $\left(\begin{array}{lll}1 & 2\end{array}\right)\left(\begin{array}{ll}1 & 2\end{array}\right)=\mathrm{id}$

Now we can check that $\tau\left(A_2\right)=\left(\begin{array}{ll}1 & 2\end{array}\right), \tau\left(A_5\right)=\left(\begin{array}{lll}1 & 2 & 3\end{array}\right)$ induces an isomorphism. We compute
$$
\begin{aligned}
& \tau\left(A_1\right)=\tau\left(A_2 A_2\right)=\tau\left(A_2\right) \tau\left(A_2\right)=\mathrm{id} \\
& \tau\left(A_3\right)=\tau\left(A_5 A_2\right)=\tau\left(A_5\right) \tau\left(A_2\right)=\left(\begin{array}{llll}
1 & 2 & 3
\end{array}\right)\left(\begin{array}{lll}
1 & 2
\end{array}\right)=\left(\begin{array}{ll}
1 & 3
\end{array}\right) \\
& \tau\left(A_4\right)=\tau\left(A_2 A_5\right)=\tau\left(A_2\right) \tau\left(A_5\right)=\left(\begin{array}{lll}
1 & 2
\end{array}\right)\left(\begin{array}{lll}
1 & 2 & 3
\end{array}\right)=\left(\begin{array}{ll}
2 & 3
\end{array}\right) \\
& \tau\left(A_6\right)=\tau\left(A_5 A_5\right)=\tau\left(A_5\right) \tau\left(A_5\right)=\left(\begin{array}{lll}
1 & 3 & 2
\end{array}\right)
\end{aligned}
$$
Thus we see that $\tau$ extendeds to an isomorphism, since $A_2$ and $A_5$ generate $T$, so that $\tau\left(A_i A_j\right)=\tau\left(A_i\right) \tau\left(A_j\right)$ follows from writing $A_i$ and $A_j$ in terms of $A_2$ and $A_5$ and using the equlities and relations shown above.
-/

theorem Herstein_exercise_4_1_34 :
    Nonempty (Equiv.Perm (Fin 3) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) := by
  classical
  -- Step 1: record the cardinalities of `GL₂(ℤ₂)` and of permutations of the three nonzero vectors.
  have hGL := card_GL_two
  have hPerm := card_perm_nonzero
  -- Step 2: turn these counts into an explicit bijection witness between the two underlying sets.
  have hCardEq : Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) =
      Fintype.card (Equiv.Perm NZ₂) := by
    simp [hGL, hPerm]
  obtain ⟨e⟩ := (Fintype.card_eq).1 hCardEq
  -- Step 3: the counting argument upgrades the injective action to a bijective homomorphism.
  have hSurj : Function.Surjective glAction :=
    Function.Injective.surjective_of_finite (e := e) glAction_injective
  -- Step 4: convert the bijective homomorphism into a multiplicative equivalence.
  have isoGLPermNZ :
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) ≃* Equiv.Perm NZ₂ :=
    MulEquiv.ofBijective glAction ⟨glAction_injective, hSurj⟩
  -- Step 5: shuttle the action along the canonical equivalence between `NZ₂` and `Fin 3`.
  let nzIso := nzEquivFin3
  have isoGLPermFin3 :
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) ≃* Equiv.Perm (Fin 3) :=
    isoGLPermNZ.trans nzIso.permCongrHom
  -- Step 6: take the symmetric of the obtained isomorphism to match the goal statement.
  exact ⟨isoGLPermFin3.symm⟩

end
