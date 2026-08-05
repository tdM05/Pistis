import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Let $G$ be a finite group and $\varphi$ an automorphism of $G$ such that $\varphi(x) = x^{-1}$ for more than three-fourths of the elements of $G$. Prove that $\varphi(y) = y^{-1}$ for all $y \in G$, and so $G$ is abelian.
-/

/-Informal Proof

Let us start with considering $b$ to be an arbitrary element in $A$. 

1. Show that $\left|A \cap\left(b^{-1} A\right)\right|>\frac{|G|}{2}$, where
$$
b^{-1} A=\left\{b^{-1} a \mid a \in A\right\}
$$
First notice that if we consider a map $f: A \rightarrow b^{-1} A$ defined by $f(a)=b^{-1} a$, for all $a \in A$, then $f$ is a 1-1 map and so $\left|b^{-1} A\right| \geq|A|>\frac{3}{4}|G|$. Now using inclusion-exclusion principle we have
$$
\left|A \cap\left(b^{-1} A\right)\right|=|A|+\left|b^{-1} A\right|-\left|A \cup\left(b^{-1} A\right)\right|>\frac{3}{4}|G|+\frac{3}{4}|G|-|G|=\frac{1}{2}|G|
$$
2. Argue that $A \cap\left(b^{-1} A\right) \subseteq C(b)$, where $C(b)$ is the centralizer of $b$ in $G$.

Suppose $x \in A \cap\left(b^{-1} A\right)$, that means, $x \in A$ and $x \in b^{-1} A$. Thus there exist an element $a \in A$ such that $x=$ $b^{-1} a$, which gives us $x b=a \in A$. Now notice that $x, b \in A$ and $x b \in A$, therefore we get
$$
\phi(x b)=(x b)^{-1} \Longrightarrow \phi(x) \phi(b)=(x b)^{-1} \Longrightarrow x^{-1} b^{-1}=b^{-1} x^{-1} \Longrightarrow x b=b x
$$
Therefore, we get $x b=b x$, for any $x \in A \cap\left(b^{-1} A\right)$, that means, $x \in C(b)$.

3. Argue that $C(b)=G$.
We know that centralizer of an element in a group $G$ is a subgroup (See Page 53). Therefore $C(b)$ is a subgroup of $G$. From statements $\mathbf{1}$ and $\mathbf{2}$, we have
$$
|C(b)| \geq\left|A \cap\left(b^{-1} A\right)\right|>\frac{|G|}{2}
$$
We need to use the following remark to argue $C(b)=G$ from the above step.
Remark. Let $G$ be a finite group and $H$ be a subgroup with more then $|G| / 2$ elements then $H=G$.

Proof of Remark. Suppose $|H|=p$ Then by Lagrange Theorem, there exist an $n \in \mathbb{N}$, such that $|G|=n p$, as $|H|$ divide $|G|$. Now by hypothesis $p>\frac{G]}{2}$ gives us,
$$
p>\frac{|G|}{2} \Longrightarrow n p>\frac{n|G|}{2} \Longrightarrow n<2 \Longrightarrow n=1
$$
Therefore we get $H=G$.

Now notice that $C(b)$ is a subgroup of $G$ with $C(b)$ having more than $|G| / 2$ elements. Therefore, $C(b)=G$.

4. Show that $A \in Z(G)$.

We know that $x \in Z(G)$ if and only if $C(a)=G$. Now notice that, for any $b \in A$ we have $C(b)=G$. Therefore, every element of $A$ is in the center of $G$, that means, $A \subseteq Z(G)$.

5. 5how that $Z(G)=G$.

As it is given that $|A|>\frac{3|G|}{4}$ and $A \leq|Z(G)|$, therefore we get
$$
|Z(G)|>\frac{3}{4}|G|>\frac{1}{2}|G| .
$$
As $Z(G)$ is a subgroup of $G$, so by the above Remark we have $Z(G)=G$. Hence $G$ is abelian.

6. Finally show that $A=G$.

First notice that $A$ is a subgroup of $G$. To show this let $p, q \in A$. Then we have
$$
\phi(p q)=\phi(p) \phi(q)=p^{-1} q^{-1}=(q p)^{-1}=(p q)^{-1}, \quad \text { As } G \text { is abelian. }
$$
Therefore, $p q \in A$ and so we have $A$ is a subgroup of $G$. Again by applying the above remark. we get $A=G$. Therefore we have
$$
\phi(y)=y^{-1}, \quad \text { for all } y \in G
$$
-/

theorem Herstein_exercise_2_5_52 {G : Type*} [Group G] [Fintype G]
  (φ : G ≃* G) {I : Finset G} (hI : ∀ x ∈ I, φ x = x⁻¹)
  (hI1 : (0.75 : ℚ) * card G ≤ card I) :
  (∀ x : G, φ x = x⁻¹) ∧ ∀ x y : G, x*y = y*x := by
  sorry

/-
Counterexample comment (why the original Lean statement is false)

The hypothesis in the Lean formulation uses the weak inequality
`(0.75 : ℚ) * card G ≤ card I`.  When `card G` is a multiple of `4`,
this allows the borderline case “exactly three quarters of the
elements”.  The informal statement, however, requires “more than
three‑fourths”.  For the dihedral group `D₈` (rotations and reflections
of a square), the identity automorphism fixes inversion on exactly six
elements (all reflections, the identity, and the half‑turn), i.e. on
`6 = (3/4) * 8` elements, but not on the two quarter‑turn rotations.
Therefore the conclusion of the Lean statement fails.
-/

/-- Step‑by‑step negation: explicit counterexample witnessing the failure
of the original Lean statement (borderline case `= 3/4`). -/
theorem Herstein_exercise_2_5_52_neg :
  ∃ (φ : DihedralGroup 4 ≃* DihedralGroup 4) (I : Finset (DihedralGroup 4)),
      (∀ x ∈ I, φ x = x⁻¹)
        ∧ (0.75 : ℚ) * card (DihedralGroup 4) ≤ card I
        ∧ ¬ ((∀ x : DihedralGroup 4, φ x = x⁻¹) ∧ ∀ x y : DihedralGroup 4, x * y = y * x) := by
  classical
  -- Step 1: pick the identity automorphism; it certainly is a multiplicative equivalence.
  let φ : DihedralGroup 4 ≃* DihedralGroup 4 := MulEquiv.refl _
  -- Step 2: take `I` to be exactly the elements fixed by inversion under `φ`
  -- (i.e. all involutions of `D₈`).
  let I : Finset (DihedralGroup 4) :=
    Finset.univ.filter (fun x : DihedralGroup 4 => φ x = x⁻¹)
  -- Step 3: package the witnesses.
  refine ⟨φ, I, ?hI, ?hCard, ?hNeg⟩
  -- Step 3.1: by construction every element of `I` satisfies the inversion condition.
  · intro x hx; exact (Finset.mem_filter.mp hx).2
  -- Step 3.2: compute cardinalities (`|D₈| = 8`, involutions = 6).
  have hCardG : card (DihedralGroup 4) = 8 := by decide
  have hCardI : I.card = 6 := by decide
  -- Step 3.3: check the (weak) ≥ 3/4 hypothesis.
  · norm_num [hCardG, hCardI]
  -- Step 3.4: exhibit that the conclusion fails (the quarter‑turn does not invert).
  · -- Step 3.4.1: the rotation by one step is not equal to its inverse.
    have h_bad :
        φ (DihedralGroup.r (1 : ZMod 4)) ≠ (DihedralGroup.r (1 : ZMod 4))⁻¹ := by
      -- `φ` is the identity, so this simplifies immediately.
      dsimp [φ]
      -- Now show `r 1 ≠ r (-1)` in `D₈`.
      decide
    -- Step 3.4.2: contradiction with the claimed conclusion.
    intro h
    exact h_bad (h.1 _)

/-
Corrected version comment

Adding a *strict* inequality “`(0.75 : ℚ) * card G < card I`” matches
the informal “more than three‑fourths”.  Under that strengthened
hypothesis the classical counting argument works: a large subset of
inverted elements forces every element to centralize it, hence the
center has size > |G|/2 and equals the whole group, making `G`
abelian.  Then the inverted set is a subgroup of index one, so
`φ x = x⁻¹` for every `x`.
-/

/-- Corrected statement with strict “more than 3/4” and detailed steps. -/
theorem Herstein_exercise_2_5_52_corrected {G : Type*} [Group G] [Fintype G]
    (φ : G ≃* G) {I : Finset G} (hI : ∀ x ∈ I, φ x = x⁻¹)
    (hI1 : (0.75 : ℚ) * card G < card I) :
    (∀ x : G, φ x = x⁻¹) ∧ ∀ x y : G, x * y = y * x := by
  classical
  -- Step 1: Package the "inverting" elements into a Finset A containing I.
  set A : Finset G := Finset.univ.filter (fun x : G => φ x = x⁻¹) with hA_def
  have hA_mem : ∀ x : G, x ∈ A ↔ φ x = x⁻¹ := fun x => by simp [A]
  have hIA : I ⊆ A := fun x hx => (hA_mem x).mpr (hI x hx)
  have hIA_card : I.card ≤ A.card := Finset.card_le_card hIA
  -- Step 2: Transfer the hypothesis to 3|G| < 4|A|.
  have h_A_big : 3 * Fintype.card G < 4 * A.card := by
    have h_card_coe : Fintype.card ↥I = I.card := Fintype.card_coe I
    have h_hyp : (0.75 : ℚ) * (Fintype.card G : ℚ) < (I.card : ℚ) := by
      have := hI1
      rw [h_card_coe] at this
      exact this
    have h_mult :
        (4 : ℚ) * ((0.75 : ℚ) * (Fintype.card G : ℚ)) < 4 * (I.card : ℚ) :=
      mul_lt_mul_of_pos_left h_hyp (by norm_num : (0 : ℚ) < 4)
    have h_ring :
        (4 : ℚ) * ((0.75 : ℚ) * (Fintype.card G : ℚ)) = 3 * (Fintype.card G : ℚ) := by
      ring
    rw [h_ring] at h_mult
    have h_IA_Q : ((I.card : ℕ) : ℚ) ≤ ((A.card : ℕ) : ℚ) := by exact_mod_cast hIA_card
    have h_Q : (3 : ℚ) * (Fintype.card G : ℚ) < 4 * (A.card : ℚ) := by linarith
    exact_mod_cast h_Q
  -- Step 3: Key lemma — any subgroup whose order exceeds |G|/2 is all of G.
  -- Stated in terms of Nat.card to avoid Fintype-instance mismatches.
  have key : ∀ (H : Subgroup G), Fintype.card G < 2 * Nat.card H → H = ⊤ := by
    intros H hH
    have h_dvd : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
    obtain ⟨k, hk⟩ := h_dvd
    have h_NG_eq : Nat.card G = Fintype.card G := Nat.card_eq_fintype_card
    have h_NH_eq : Nat.card H = Fintype.card H := Nat.card_eq_fintype_card
    have h_G_pos : 0 < Nat.card G := by rw [h_NG_eq]; exact Fintype.card_pos
    have h_H_pos : 0 < Nat.card H := by rw [h_NH_eq]; exact Fintype.card_pos
    have h_k_pos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · exfalso
        rw [h0, Nat.mul_zero] at hk
        omega
      · exact hpos
    have h_k_lt : k < 2 := by
      by_contra hle
      push_neg at hle
      have h1 : Nat.card H * 2 ≤ Nat.card H * k := Nat.mul_le_mul_left _ hle
      rw [← hk, h_NG_eq] at h1
      omega
    have h_k_eq : k = 1 := by omega
    have h_card_NG_eq_NH : Nat.card G = Nat.card H := by
      rw [hk, h_k_eq, Nat.mul_one]
    have h_F_eq : Fintype.card H = Fintype.card G := by
      calc Fintype.card H = Nat.card H := h_NH_eq.symm
        _ = Nat.card G := h_card_NG_eq_NH.symm
        _ = Fintype.card G := h_NG_eq
    -- Translate equal cardinalities into H = ⊤ via filter/univ.
    have h_filter_card :
        (Finset.univ.filter (fun x : G => x ∈ H)).card = Fintype.card H := by
      rw [← Fintype.card_subtype]
    have h_filter_univ :
        Finset.univ.filter (fun x : G => x ∈ H) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [h_filter_card]; exact h_F_eq)
    ext x
    refine ⟨fun _ => Subgroup.mem_top x, fun _ => ?_⟩
    have hx_filter : x ∈ Finset.univ.filter (fun x : G => x ∈ H) := by
      rw [h_filter_univ]; exact Finset.mem_univ x
    exact (Finset.mem_filter.mp hx_filter).2
  -- Helper: if every element of S lies in a subgroup K, then |S| ≤ |K|.
  have helper_card :
      ∀ (K : Subgroup G) (S : Finset G), (∀ y ∈ S, y ∈ K) → S.card ≤ Nat.card K := by
    intro K S hSK
    have h_sub : S ⊆ Finset.univ.filter (fun x : G => x ∈ K) := by
      intros y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hSK y hy
    have h_le : S.card ≤ (Finset.univ.filter (fun x : G => x ∈ K)).card :=
      Finset.card_le_card h_sub
    have h_filter_card :
        (Finset.univ.filter (fun x : G => x ∈ K)).card = Fintype.card K := by
      rw [← Fintype.card_subtype]
    rw [h_filter_card] at h_le
    rw [Nat.card_eq_fintype_card]
    exact h_le
  -- Step 4: For every b ∈ A and every x ∈ G, b and x commute.
  have h_mul_comm_A : ∀ b ∈ A, ∀ x : G, b * x = x * b := by
    intros b hb x
    -- Step 4.1: Translate A by b⁻¹ on the left.
    let bA : Finset G := A.image (fun a : G => b⁻¹ * a)
    have h_bA_card : bA.card = A.card :=
      Finset.card_image_of_injective A (fun _ _ h => mul_left_cancel h)
    have h_bA_mem : ∀ y, y ∈ bA ↔ b * y ∈ A := by
      intro y
      simp only [bA, Finset.mem_image]
      constructor
      · rintro ⟨a, ha, rfl⟩
        have : b * (b⁻¹ * a) = a := by group
        rw [this]; exact ha
      · intro hby
        refine ⟨b * y, hby, ?_⟩
        group
    -- Step 4.2: The intersection S = A ∩ bA has > |G|/2 elements
    -- (from 3|G| < 4|A| and inclusion–exclusion).
    let S : Finset G := A ∩ bA
    have h_S_big : Fintype.card G < 2 * S.card := by
      have h_union_le : (A ∪ bA).card ≤ Fintype.card G := by
        have h_sub : A ∪ bA ⊆ Finset.univ := Finset.subset_univ _
        have := Finset.card_le_card h_sub
        simpa using this
      have h_ie : S.card + (A ∪ bA).card = A.card + bA.card :=
        Finset.card_inter_add_card_union A bA
      rw [h_bA_card] at h_ie
      omega
    -- Step 4.3: Every y ∈ S commutes with b.
    have h_S_comm : ∀ y ∈ S, b * y = y * b := by
      intros y hy
      have hyA : y ∈ A := (Finset.mem_inter.mp hy).1
      have hybA : y ∈ bA := (Finset.mem_inter.mp hy).2
      have hby : b * y ∈ A := (h_bA_mem y).mp hybA
      have h_phi_y : φ y = y⁻¹ := (hA_mem y).mp hyA
      have h_phi_b : φ b = b⁻¹ := (hA_mem b).mp hb
      have h_phi_by : φ (b * y) = (b * y)⁻¹ := (hA_mem _).mp hby
      have h1 : φ (b * y) = b⁻¹ * y⁻¹ := by rw [map_mul, h_phi_b, h_phi_y]
      have h2 : (b * y)⁻¹ = y⁻¹ * b⁻¹ := mul_inv_rev b y
      have h_eq : b⁻¹ * y⁻¹ = y⁻¹ * b⁻¹ := by rw [← h1, h_phi_by, h2]
      have h_inv : (b⁻¹ * y⁻¹)⁻¹ = (y⁻¹ * b⁻¹)⁻¹ := congrArg Inv.inv h_eq
      simp only [mul_inv_rev, inv_inv] at h_inv
      exact h_inv.symm
    -- Step 4.4: The centralizer of {b} has order > |G|/2, hence equals G.
    let Cb : Subgroup G := Subgroup.centralizer ({b} : Set G)
    have h_S_sub_Cb : ∀ y ∈ S, y ∈ Cb := by
      intros y hy
      show y ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_iff]
      intros z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact h_S_comm y hy
    have h_Cb_card_ge : S.card ≤ Nat.card Cb := helper_card Cb S h_S_sub_Cb
    have h_Cb_top : Cb = ⊤ := key Cb (by omega)
    have h_x_in_Cb : x ∈ Cb := by rw [h_Cb_top]; exact Subgroup.mem_top x
    have h_centralize : ∀ h ∈ ({b} : Set G), h * x = x * h :=
      Subgroup.mem_centralizer_iff.mp h_x_in_Cb
    exact h_centralize b (Set.mem_singleton b)
  -- Step 5: The center of G contains A, so |Z(G)| > |G|/2 and Z(G) = G.
  have h_abelian : ∀ x y : G, x * y = y * x := by
    let Z : Subgroup G := Subgroup.center G
    have h_A_sub_Z : ∀ a ∈ A, a ∈ Z := by
      intros a ha
      rw [Subgroup.mem_center_iff]
      intro g
      exact (h_mul_comm_A a ha g).symm
    have h_Z_card_ge : A.card ≤ Nat.card Z := helper_card Z A h_A_sub_Z
    have h_Z_top : Z = ⊤ := key Z (by omega)
    intros x y
    have h_x_in_Z : x ∈ Z := by rw [h_Z_top]; exact Subgroup.mem_top x
    exact (Subgroup.mem_center_iff.mp h_x_in_Z y).symm
  -- Step 6: In the now‑abelian group, A is a subgroup; |A| > |G|/2 forces A = G.
  refine ⟨?_, h_abelian⟩
  intro x
  let Asub : Subgroup G :=
    { carrier := {z | φ z = z⁻¹}
      one_mem' := by
        show φ (1 : G) = (1 : G)⁻¹
        rw [map_one, inv_one]
      mul_mem' := by
        intros a b ha hb
        show φ (a * b) = (a * b)⁻¹
        have ha' : φ a = a⁻¹ := ha
        have hb' : φ b = b⁻¹ := hb
        rw [map_mul, ha', hb', mul_inv_rev]
        exact h_abelian a⁻¹ b⁻¹
      inv_mem' := by
        intros a ha
        show φ a⁻¹ = (a⁻¹)⁻¹
        have ha' : φ a = a⁻¹ := ha
        rw [map_inv, ha'] }
  have h_A_sub_Asub : ∀ a ∈ A, a ∈ Asub := fun a ha => (hA_mem a).mp ha
  have h_Asub_card_ge : A.card ≤ Nat.card Asub :=
    helper_card Asub A h_A_sub_Asub
  have h_Asub_top : Asub = ⊤ := key Asub (by omega)
  have h_x_in_Asub : x ∈ Asub := by rw [h_Asub_top]; exact Subgroup.mem_top x
  exact h_x_in_Asub
