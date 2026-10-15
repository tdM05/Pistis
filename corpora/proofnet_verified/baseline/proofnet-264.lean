import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $\varphi$ is a homomorphism of $G$ onto $G'$ and $N \triangleleft G$, show that $\varphi(N) \triangleleft G'$.
-/

/-Informal Proof

We first claim that $\varphi(N)$ is a subgroup of $G'$. To see this, note that since $N$ is a subgroup of $G$, the identity element $e_G$ of $G$ belongs to $N$. Therefore, the element $\varphi(e_G) \in \varphi(N)$, so $\varphi(N)$ is a non-empty subset of $G'$.

Now, let $a', b' \in \varphi(N)$. Then there exist elements $a, b \in N$ such that $\varphi(a) = a'$ and $\varphi(b) = b'$. Since $N$ is a subgroup of $G$, we have $a, b \in N$, so $ab^{-1} \in N$. Thus, we have
$$\varphi(ab^{-1}) = \varphi(a) \varphi(b^{-1}) = a'b'^{-1} \in \varphi(N),$$
which shows that $a', b' \in \varphi(N)$ implies $a'b'^{-1} \in \varphi(N)$. Therefore, $\varphi(N)$ is a subgroup of $G'$.

Next, we will show that $\varphi(N)$ is a normal subgroup of $G'$. Let $\varphi(N) = N'$, a subgroup of $G'$. Let $x' \in G'$ and $h' \in N'$. Since $\varphi$ is onto, there exist elements $x \in G$ and $h \in N$ such that $\varphi(x) = x'$ and $\varphi(h) = h'$.

Since $N$ is a normal subgroup of $G$, we have $xhx^{-1} \in N$. Thus,
$$\varphi(xhx^{-1}) = \varphi(x)\varphi(h)\varphi(x^{-1}) = x'h'x'^{-1} \in \varphi(N),$$
which shows that $x' \in G'$ and $h' \in N'$ implies $x'h'x'^{-1} \in \varphi(N)$. Therefore, $\varphi(N)$ is a normal subgroup of $G'$. This completes the proof.
-/

theorem Herstein_exercise_2_7_7 {G : Type*} [Group G] {G' : Type*} [Group G']
  (φ : G →* G') (N : Subgroup G) [N.Normal] :
  (Subgroup.map φ N).Normal  := by
  sorry

/-
The formal statement above forgets the hypothesis that `φ` is surjective. Without
that hypothesis the conclusion can fail: take `G` to be the order-two subgroup
`{(), (0 1)}` inside `S₃`, let `φ` be the inclusion into `S₃`, and take the normal
subgroup `N = G`. Then `φ(N)` is exactly that order-two subgroup, which is not
normal inside the whole symmetric group `S₃`, because conjugating `(0 1)` by
`(1 2)` produces `(0 2)` which no longer lies inside `{(), (0 1)}`. The proofs
below formalize this counterexample, prove the negation of the original statement,
and then give the corrected version that assumes surjectivity.
-/

namespace Proofnet264

open Equiv

private def swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
private def swap02 : Equiv.Perm (Fin 3) := Equiv.swap 0 2
private def swap12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

@[simp] lemma swap01_sq : swap01 * swap01 = (1 : Equiv.Perm (Fin 3)) := by
  classical
  -- Step 1: Apply the general fact `Equiv.swap_mul_self` to the specific swap `(0 1)`.
  simp [swap01, Equiv.swap_mul_self (0 : Fin 3) 1]

@[simp] lemma swap01_inv : (swap01 : Equiv.Perm (Fin 3))⁻¹ = swap01 := by
  classical
  -- Step 1: Use that any swap is an involution (`Equiv.swap_inv`).
  simp [swap01, Equiv.swap_inv (0 : Fin 3) 1]

@[simp] lemma swap12_inv : (swap12 : Equiv.Perm (Fin 3))⁻¹ = swap12 := by
  classical
  -- Step 1: Use the same involution fact for the swap `(1 2)`.
  simp [swap12, Equiv.swap_inv (1 : Fin 3) 2]

@[simp] lemma swap12_sq : swap12 * swap12 = (1 : Equiv.Perm (Fin 3)) := by
  classical
  -- Step 1: Apply `Equiv.swap_mul_self` to `(1 2)`.
  simp [swap12, Equiv.swap_mul_self (1 : Fin 3) 2]

def twoCycleSubgroup : Subgroup (Equiv.Perm (Fin 3)) where
  carrier := {σ | σ = 1 ∨ σ = swap01}
  one_mem' := by
    -- Step 1: The identity permutation satisfies the left disjunct.
    left; rfl
  mul_mem' := by
    classical
    -- Step 1: Case distinction on whether the first factor is `1` or `swap01`.
    intro a b ha hb
    have ha' : a = 1 ∨ a = swap01 := ha
    cases ha' with
    | inl ha1 =>
        -- Step 1.1: If `a = 1`, the product simplifies to `b`.
        have hb' : b = 1 ∨ b = swap01 := hb
        cases hb' with
        | inl hb1 =>
            -- Step 1.1.1: `b = 1`, hence the product is `1`.
            left
            simp [ha1, hb1]
        | inr hb1 =>
            -- Step 1.1.2: `b = swap01`, hence the product is `swap01`.
            right
            simp [ha1, hb1]
    | inr ha1 =>
        -- Step 1.2: `a = swap01`.
        have hb' : b = 1 ∨ b = swap01 := hb
        cases hb' with
        | inl hb1 =>
            -- Step 1.2.1: `b = 1`, so the product is `swap01`.
            right
            simp [ha1, hb1]
        | inr hb1 =>
            -- Step 1.2.2: `b = swap01`, so the product is `swap01 * swap01 = 1`.
            left
            simp [ha1, hb1, swap01_sq]
  inv_mem' := by
    classical
    -- Step 1: Break into the same two cases as above.
    intro a ha
    have ha' : a = 1 ∨ a = swap01 := ha
    cases ha' with
    | inl ha1 =>
        -- Step 1.1: The inverse of `1` is `1`.
        left
        simp [ha1]
    | inr ha1 =>
        -- Step 1.2: The inverse of `swap01` is `swap01`.
        right
        simp [ha1, swap01_inv]

@[simp] lemma mem_twoCycleSubgroup {σ : Equiv.Perm (Fin 3)} :
    σ ∈ twoCycleSubgroup ↔ σ = 1 ∨ σ = swap01 := Iff.rfl

def inclusionHom : twoCycleSubgroup →* Equiv.Perm (Fin 3) where
  toFun := fun g => g
  map_one' := rfl
  map_mul' := by
    -- Step 1: The inclusion is the identity on multiplication.
    intro a b
    rfl

lemma map_top_eq_twoCycleSubgroup :
    Subgroup.map inclusionHom (⊤ : Subgroup twoCycleSubgroup) = twoCycleSubgroup := by
  classical
  -- Step 1: Show both sides have the same elements.
  ext σ
  constructor
  · -- Step 1.1: Any element in the map has a preimage inside `twoCycleSubgroup`.
    rintro ⟨x, -, rfl⟩
    -- Step 1.1.1: The coercion records that `x` belongs to `twoCycleSubgroup`.
    exact x.property
  · -- Step 1.2: Any element of `twoCycleSubgroup` lifts to an element of `⊤`.
    intro hσ
    refine ⟨⟨σ, hσ⟩, ?_, rfl⟩
    -- Step 1.2.1: Every element of `⊤` is admitted automatically.
    simp

abbrev counterexampleGroup := ULift (↥twoCycleSubgroup)

def counterexampleHom : counterexampleGroup →* Equiv.Perm (Fin 3) where
  toFun := fun g => g.down
  map_one' := by
    -- Step 1: The lifted identity reduces immediately to the identity permutation.
    rfl
  map_mul' := by
    -- Step 1: Multiplication also acts pointwise under the `ULift`.
    intro a b
    rfl

lemma map_top_counterexampleHom :
    Subgroup.map counterexampleHom (⊤ : Subgroup counterexampleGroup) = twoCycleSubgroup := by
  classical
  -- Step 1: Compare both sides elementwise.
  ext σ
  constructor
  · -- Step 1.1: Any element of the image comes from an element in the lifted subgroup.
    rintro ⟨x, -, hx⟩
    rcases x with ⟨⟨t, ht⟩⟩
    have hx' : t = σ := by
      simpa [counterexampleHom] using hx
    cases ht with
    | inl ht1 =>
        -- Step 1.1.1: Conclude `σ = 1`.
        left
        simpa [hx'] using ht1
    | inr ht1 =>
        -- Step 1.1.2: Conclude `σ = swap01`.
        right
        simpa [hx'] using ht1
  · -- Step 1.2: Every element of `twoCycleSubgroup` admits a lifted preimage.
    intro hσ
    refine ⟨⟨⟨σ, hσ⟩⟩, ?_, ?_⟩
    · -- Step 1.2.1: Lifted elements automatically lie in `⊤`.
      simp
    · -- Step 1.2.2: Evaluate the homomorphism.
      rfl

lemma swap02_not_mem : swap02 ∉ twoCycleSubgroup := by
  classical
  -- Step 1: Show that `swap02` differs from both `1` and `swap01`.
  have hneq1 : swap02 ≠ (1 : Equiv.Perm (Fin 3)) := by
    -- Step 1.1: Direct computation shows the permutations differ.
    decide
  have hneqswap : swap02 ≠ swap01 := by
    -- Step 1.2: Likewise, the transpositions act on different points.
    decide
  -- Step 2: Assume for contradiction that `swap02` lies in the subgroup.
  intro hmem
  -- Step 3: Use the explicit description to derive the contradiction.
  cases (mem_twoCycleSubgroup).1 hmem with
  | inl h => exact hneq1 h
  | inr h => exact hneqswap h

lemma conj_swap (f : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    f * Equiv.swap i j * f⁻¹ = Equiv.swap (f i) (f j) := by
  classical
  -- Step 1: Apply the formula `mul_swap_eq_swap_mul` and then cancel `f`.
  have h := Equiv.mul_swap_eq_swap_mul f i j
  calc
    f * Equiv.swap i j * f⁻¹
        = (Equiv.swap (f i) (f j) * f) * f⁻¹ := by simp [h]
    _ = Equiv.swap (f i) (f j) := by
      -- Step 1.1: Use associativity and `f * f⁻¹ = 1`.
      simp [mul_assoc]

lemma swap12_conj_swap01 :
    (swap12 : Equiv.Perm (Fin 3)) * swap01 * swap12⁻¹ = swap02 := by
  classical
  -- Step 1: Use the general conjugation lemma with `i = 0`, `j = 1`.
  have h := conj_swap swap12 (0 : Fin 3) 1
  -- Step 2: Simplify the images `swap12 0 = 0` and `swap12 1 = 2`.
  simpa [swap12, swap01, swap02]

lemma swap12_conj_swap01_no_inv :
    (swap12 : Equiv.Perm (Fin 3)) * swap01 * swap12 = swap02 := by
  classical
  -- Step 1: Remove the inverse using `swap12_inv`.
  simpa [swap12_inv] using swap12_conj_swap01

lemma twoCycleSubgroup_not_normal : ¬ twoCycleSubgroup.Normal := by
  classical
  -- Step 1: Suppose for contradiction that the subgroup is normal.
  intro hNormal
  -- Step 2: Record that the transposition `(0 1)` belongs to the subgroup.
  have hswap01 : swap01 ∈ twoCycleSubgroup := by
    -- Step 2.1: This follows from the right disjunct in the definition.
    exact (mem_twoCycleSubgroup).2 (Or.inr rfl)
  -- Step 3: Apply normality to the conjugation by `(1 2)`.
  have hconj := hNormal.conj_mem swap01 hswap01 swap12
  -- Step 4: Simplify the resulting conjugate using `swap12_conj_swap01`.
  have hswap02 : swap02 ∈ twoCycleSubgroup := by
    -- Step 4.1: Use the explicit description of the conjugate.
    simpa [swap12_conj_swap01_no_inv] using hconj
  -- Step 5: Contradict the previously proved non-membership of `swap02`.
  exact swap02_not_mem hswap02

theorem Herstein_exercise_2_7_7_neg :
    ∃ (G : Type) (_ : Group G) (G' : Type) (_ : Group G')
      (φ : G →* G') (N : Subgroup G), N.Normal ∧ ¬ (Subgroup.map φ N).Normal := by
  classical
  -- Step 1: Choose `G` to be the lifted two-element subgroup of `S₃`, and `G' = S₃`.
  refine ⟨counterexampleGroup, inferInstance, Equiv.Perm (Fin 3), inferInstance,
    counterexampleHom, ⊤, ?_, ?_⟩
  · -- Step 2: The top subgroup is normal in any group.
    infer_instance
  · -- Step 3: The image coincides with `twoCycleSubgroup`, which is not normal.
    have hmap :
        Subgroup.map counterexampleHom (⊤ : Subgroup counterexampleGroup) = twoCycleSubgroup :=
      map_top_counterexampleHom
    have hNormal : ¬ twoCycleSubgroup.Normal := twoCycleSubgroup_not_normal
    -- Step 3.1: Translate the non-normality statement via `hmap`.
    have hImageNotNormal :
        ¬ (Subgroup.map counterexampleHom (⊤ : Subgroup counterexampleGroup)).Normal := by
      intro hMapNormal
      have hSub : twoCycleSubgroup.Normal := by
        simpa using (hmap ▸ hMapNormal)
      exact hNormal hSub
    exact hImageNotNormal

/-
Corrected statement:
If `φ : G →* G'` is surjective and `N` is normal in `G`, then the image
`Subgroup.map φ N` is normal in `G'`. The proof mirrors the informal argument:
take a preimage `g` of any `g' : G'`, take a preimage `n` of any `n'` in the
image, use the normality of `N` to see that `g * n * g⁻¹` is still in `N`, and
apply `φ` to show that `g' * n' * g'⁻¹` returns to the image.
-/

theorem Herstein_exercise_2_7_7_corrected {G : Type*} [Group G] {G' : Type*} [Group G']
    (φ : G →* G') (hφ : Function.Surjective φ) (N : Subgroup G) [N.Normal] :
    (Subgroup.map φ N).Normal := by
  classical
  -- Step 1: Expand the definition of normality for `Subgroup.map φ N`.
  refine ⟨?_⟩
  -- Step 2: Fix an element `n'` of the image and unpack its preimage.
  intro n' hn'
  rcases hn' with ⟨n, hnN, rfl⟩
  -- Step 3: Fix an arbitrary `g' : G'` and pick a preimage `g`.
  intro g'
  obtain ⟨g, rfl⟩ := hφ g'
  -- Step 4: Use the normality of `N` to keep conjugates inside `N`.
  have hconj : g * n * g⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem n hnN g
  -- Step 5: Exhibit the conjugate as an element of the map with the right image.
  refine ⟨g * n * g⁻¹, hconj, ?_⟩
  -- Step 6: Evaluate `φ` on that conjugate to obtain `g' * n' * g'⁻¹`.
  simp [map_mul, map_inv, mul_assoc]

end Proofnet264
