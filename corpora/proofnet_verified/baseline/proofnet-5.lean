import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Let $Z$ be the center of a group $G$. Prove that if $G / Z$ is a cyclic group, then $G$ is abelian and hence $G=Z$.
-/

/-Informal Proof

We have that $G / Z(G)$ is cyclic, and so there is an element $x \in G$ such that $G / Z(G)=\langle x Z(G)\rangle$, where $x Z(G)$ is the coset with representative $x$. Now let $g \in G$
We know that $g Z(G)=(x Z(G))^m$ for some $m$, and by definition $(x Z(G))^m=x^m Z(G)$.
Now, in general, if $H \leq G$, we have by definition too that $a H=b H$ if and only if $b^{-1} a \in H$.
In our case, we have that $g Z(G)=x^m Z(G)$, and this happens if and only if $\left(x^m\right)^{-1} g \in Z(G)$.
Then, there's a $z \in Z(G)$ such that $\left(x^m\right)^{-1} g=z$, and so $g=x^m z$.

$g, h \in G$ implies that $g=x^{a_1} z_1$ and $h=x^{a_2} z_2$, so
$$
\begin{aligned}
g h & =\left(x^{a_1} z_1\right)\left(x^{a_2} z_2\right) \\
& =x^{a_1} x^{a_2} z_1 z_2 \\
& =x^{a_1+a_2} z_2 z_1 \\
& =\ldots=\left(x^{a_2} z_2\right)\left(x^{a_1} z_1\right)=h g .
\end{aligned}
$$
Therefore, $G$ is abelian.
-/

theorem Artin_exercise_6_1_14 (G : Type*) [Group G]
  (hG : IsCyclic $ G ⧸ (center G)) :
  center G = ⊤ := by
  -- Step 1: Work in a classical environment to freely choose witnesses.
  classical
  -- Step 2: Obtain a generator of the cyclic quotient together with the covering property.
  obtain ⟨gbar, hgbar⟩ := hG.exists_generator
  -- Step 2.1: Choose a representative `g : G` of the generator `ḡ` in the quotient.
  obtain ⟨g, rfl⟩ := Quot.exists_rep gbar
  -- Step 2.2: Record the canonical quotient homomorphism once and for all.
  let q : G →* G ⧸ center G := QuotientGroup.mk' (center G)
  -- Step 3: Show that every element of `G` splits into a power of `g` times a central element.
  have h_decomp : ∀ x : G, ∃ n : ℤ, ∃ z : center G, x = g ^ n * z := by
    intro x
    -- Step 3.1: Use the generator property to express the coset of `x` as a power of `q g`.
    have hx_mem : q x ∈ Subgroup.zpowers (q g) := by
      simpa using hgbar (q x)
    -- Step 3.2: Extract an explicit exponent witnessing membership in the cyclic subgroup.
    rcases Subgroup.mem_zpowers_iff.mp hx_mem with ⟨n, hn⟩
    -- Step 3.3: Translate the equality in the quotient back to a statement in `G`.
    have hx_pow : q x = (q g) ^ n := by
      simpa using hn.symm
    -- Step 3.4: Verify that the quotient of `x` by `g ^ n` lands in the kernel, i.e. the center.
    have hx_one' : q ((g ^ n)⁻¹ * x) = 1 := by
      calc
        q ((g ^ n)⁻¹ * x)
            = q (g ^ n)⁻¹ * q x := by
              simp [map_mul, map_inv]
        _ = ((q g) ^ n)⁻¹ * (q g) ^ n := by
              simp [map_zpow, hx_pow]
        _ = 1 := by simp
    have hx_one : ((g ^ n)⁻¹ * x : G ⧸ center G) = 1 := by
      simpa [q] using hx_one'
    have hx_center : (g ^ n)⁻¹ * x ∈ center G :=
      (QuotientGroup.eq_one_iff (N := center G) ((g ^ n)⁻¹ * x)).1 hx_one
    -- Step 3.5: Package the central element and rewrite `x` accordingly.
    set z : center G := ⟨(g ^ n)⁻¹ * x, hx_center⟩
    refine ⟨n, z, ?_⟩
    -- Step 3.6: Finish the algebra showing `x = g ^ n * z` for the chosen central element.
    have : g ^ n * ((g ^ n)⁻¹ * x) = x := by
      simp
    simp [z]
  -- Step 4: Prove that any two elements of `G` commute using the above decomposition.
  have h_comm : ∀ x y : G, x * y = y * x := by
    intro x y
    -- Step 4.1: Decompose both `x` and `y` into a power of `g` times a central element.
    obtain ⟨nx, zx, hx⟩ := h_decomp x
    obtain ⟨ny, zy, hy⟩ := h_decomp y
    -- Step 4.2: Record the useful commutation facts stemming from centrality.
    have h_zx_comm : ∀ h : G, (zx : G) * h = h * (zx : G) := by
      intro h
      simpa using (Subgroup.mem_center_iff.mp zx.property h).symm
    have h_zy_comm : ∀ h : G, (zy : G) * h = h * (zy : G) := by
      intro h
      simpa using (Subgroup.mem_center_iff.mp zy.property h).symm
    -- Step 4.3: Convert centrality information into the explicit commutation equalities we need.
    have hzx_gn : Commute (zx : G) (g ^ nx) := h_zx_comm _
    have hzx_gm : Commute (zx : G) (g ^ ny) := h_zx_comm _
    have hzy_gn : Commute (zy : G) (g ^ nx) := h_zy_comm _
    have hzy_gm : Commute (zy : G) (g ^ ny) := h_zy_comm _
    have hz_comm : Commute (zx : G) (zy : G) := h_zx_comm _
    -- Step 4.4: Powers of the same element commute automatically.
    have h_pow_comm : Commute (g ^ nx) (g ^ ny) := (Commute.refl g).zpow_zpow _ _
    -- Step 4.5: Assemble all commutation relations to show `x` and `y` commute.
    have h_gn_zy : Commute (g ^ nx) (zy : G) := (hzy_gn).symm
    have h_zx_right : Commute (zx : G) (g ^ ny * (zy : G)) := hzx_gm.mul_right hz_comm
    have h_left := h_pow_comm.mul_right h_gn_zy
    have hx_comm : Commute (g ^ nx * (zx : G)) (g ^ ny * (zy : G)) := h_left.mul_left h_zx_right
    -- Step 4.6: Rewrite the original elements back and extract the commuting equality.
    have := hx_comm.eq
    simpa [hx, hy] using this
  -- Step 5: Every element belongs to the center thanks to the previous commutativity result.
  have h_all_center : ∀ x : G, x ∈ center G := by
    intro x
    refine (Subgroup.mem_center_iff).2 ?_
    intro y
    simpa using h_comm y x
  -- Step 6: Conclude that the center equals the whole group.
  apply le_antisymm le_top
  intro x _; exact h_all_center x
