import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Suppose that $G$ is an abelian group of order $p^nm$ where $p \nmid m$ is a prime.  If $H$ is a subgroup of $G$ of order $p^n$, prove that $H$ is a characteristic subgroup of $G$.
-/

/-Informal Proof

Let $G$ be an abelian group of order $p^n m$, such that $p \nmid m$. Now, Given that $H$ is a subgroup of order $p^n$. Since $G$ is abelian $H$ is normal. Now we want to prove that $H$ is a characteristic subgroup, that is $\phi(H)=H$ for any automorphism $\phi$ of $G$. Now consider $\phi(H)$. Clearly $|\phi(H)|=p^n$. Suppose $\phi(H) \neq H$, then $|H \cap \phi(H)|=p^s$, where $s<n$. Consider $H \phi(H)$, this is a subgroup of $G$ as $H$ is normal. Also $|H \phi(H)|=\frac{|H||\phi(H)|}{|H \cap \phi(H)|}=\frac{p^{2 n}}{p^s}=p^{2 n-s}$, where $2 n-s>n$. By lagrange's theorem then $p^{2 n-s}\left|p^n m \Longrightarrow p^{n-s}\right| m \Longrightarrow p \mid m$-contradiction. So $\phi(H)=H$, and $H$ is characteristic subgroup of $G$.
-/

theorem Herstein_exercise_2_5_31 {G : Type*} [CommGroup G] [Fintype G]
  {p m n : ℕ} (hp : Nat.Prime p) (hp1 : ¬ p ∣ m) (hG : card G = p^n*m)
  {H : Subgroup G} [Fintype H] (hH : card H = p^n) :
  Subgroup.Characteristic H := by
  classical
  -- Step 1: Register the prime hypothesis as a `Fact` so the Sylow API can use it seamlessly.
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  -- Step 2: Rewrite the group and subgroup cardinalities in terms of `Nat.card` for arithmetic.
  have hCardH : Nat.card ↥H = p^n := by
    -- Step 2.1: `Nat.card` and `Fintype.card` agree, so we can reuse the hypothesis `hH` directly.
    simpa [Nat.card_eq_fintype_card] using hH
  have hCardG : Nat.card G = p^n * m := by
    -- Step 2.2: Apply the same translation for the ambient group `G`.
    simpa [Nat.card_eq_fintype_card] using hG
  -- Step 3: Use Lagrange’s theorem to compute the index of `H` explicitly.
  have hLagrange : card H * H.index = card G := by
    -- Step 3.1: Invoke the standard cardinality-index relation.
    simpa [Nat.card_eq_fintype_card] using
      (Subgroup.card_mul_index (H := H))
  have hIndexEq : p^n * H.index = p^n * m := by
    -- Step 3.2: Substitute the known values of `card H` and `card G`.
    simpa [hH, hG, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hLagrange
  have hIndex : H.index = m := by
    -- Step 3.3: Cancel the positive factor `p^n` from both sides of the previous equality.
    have hpow_pos : 0 < p^n := Nat.pow_pos (Nat.Prime.pos hp)
    exact Nat.mul_left_cancel hpow_pos hIndexEq
  -- Step 4: Transport the coprimality information from `m` to the index of `H`.
  have hIndexNot : ¬ p ∣ H.index := by
    -- Step 4.1: Show that divisibility of the index would contradict the hypothesis for `m`.
    intro hdiv
    exact hp1 (by simpa [hIndex] using hdiv)
  -- Step 5: Recognize that `H` is a `p`-group because its order is a pure power of `p`.
  have hIsP : IsPGroup p H := by
    -- Step 5.1: Invoke the basic `p`-group constructor supplied by the cardinality equality.
    exact IsPGroup.of_card hCardH
  -- Step 6: View `H` as an actual Sylow `p`-subgroup of `G` via the universal property of `IsPGroup`.
  let P : Sylow p G := hIsP.toSylow (G := G) hIndexNot
  have hP_sub : (P : Subgroup G) = H := by
    -- Step 6.1: Unfold the coercion to substantiate that the constructed Sylow subgroup coincides with `H`.
    change (hIsP.toSylow (G := G) hIndexNot : Subgroup G) = H
    simp [IsPGroup.toSylow_coe]
  -- Step 7: Transfer the obvious normality of `H` (automatic in abelian groups) to the Sylow subgroup `P`.
  have hP_normal : P.Normal := by
    -- Step 7.1: Obtain the inherent normality of `H` from commutativity and transport it along the equality above.
    have hH_normal : H.Normal := inferInstance
    simpa [hP_sub] using hH_normal
  -- Step 8: A normal Sylow subgroup is characteristic, so this property holds for `P`.
  have hP_char : P.Characteristic :=
    Sylow.characteristic_of_normal (G := G) P hP_normal
  -- Step 9: Translate the characteristic property back to the original subgroup `H`.
  simpa [hP_sub] using hP_char
