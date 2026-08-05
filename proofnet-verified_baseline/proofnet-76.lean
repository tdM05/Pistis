import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Suppose that $|G| = pm$, where $p \nmid m$ and $p$ is a prime. If $H$ is a normal subgroup of order $p$ in $G$, prove that $H$ is characteristic.
-/

/-Informal Proof

Let $G$ be a group of order $p m$, such that $p \nmid m$. Now, Given that $H$ is a normal subgroup of order $p$. Now we want to prove that $H$ is a characteristic subgroup, that is $\phi(H)=H$ for any automorphism $\phi$ of $G$. Now consider $\phi(H)$. Clearly $|\phi(H)|=p$. Suppose $\phi(H) \neq H$, then $H \cap \phi (H)=\{ e\}$. Consider $H \phi(H)$, this is a subgroup of $G$ as $H$ is normal. Also $|H \phi(H)|=p^2$. By lagrange's theorem then $p^2 \mid$ $p m \Longrightarrow p \mid m$ - contradiction. So $\phi(H)=H$, and $H$ is characteristic subgroup of $G$
-/

theorem Herstein_exercise_2_5_30 {G : Type*} [Group G] [Fintype G]
  {p m : ℕ} (hp : Nat.Prime p) (hp1 : ¬ p ∣ m) (hG : card G = p*m)
  {H : Subgroup G} [Fintype H] [H.Normal] (hH : card H = p):
  Subgroup.Characteristic H := by
  classical
  -- Step 1: View the prime as a typeclass assumption for Sylow theory.
  haveI : Fact p.Prime := ⟨hp⟩
  -- Step 2: Translate the given cardinalities to the `Nat.card` formulation.
  have hCardH : Nat.card (↥H) = p := by
    simpa [Nat.card_eq_fintype_card] using hH
  have hCardG : Nat.card G = p * m := by
    simpa [Nat.card_eq_fintype_card] using hG
  -- Step 3: Evaluate the index of `H` using Lagrange’s theorem.
  have hIndexEq : Nat.card (↥H) * H.index = Nat.card G :=
    Subgroup.card_mul_index (H := H)
  have hIndex : H.index = m := by
    -- Step 3.1: Rewrite the Lagrange equality using the information about sizes.
    have hWorking := hIndexEq
    rw [hCardH, hCardG] at hWorking
    have : H.index * p = m * p := by
      simpa [Nat.mul_comm] using hWorking
    -- Step 3.2: Cancel the common factor `p` using its positivity.
    exact Nat.mul_right_cancel hp.pos this
  -- Step 4: Extract that the index of `H` is coprime to `p`.
  have hIndexNot : ¬ p ∣ H.index := by
    simpa [hIndex] using hp1
  -- Step 5: Observe that `H` is a `p`-group thanks to its order.
  have hIsP : IsPGroup p H := by
    have : Nat.card (↥H) = p ^ 1 := by simpa [hCardH, pow_one]
    exact IsPGroup.of_card this
  -- Step 6: Bundle `H` as an actual Sylow subgroup of `G`.
  let P : Sylow p G := hIsP.toSylow (G := G) hIndexNot
  have hP_sub : (P : Subgroup G) = H := by
    -- Step 6.1: Unfold the definition of `P` and apply the canonical equality.
    change (hIsP.toSylow (G := G) hIndexNot : Subgroup G) = H
    simp [IsPGroup.toSylow_coe]
  -- Step 7: Inherit normality from `H` to the constructed Sylow subgroup `P`.
  have hP_normal : P.Normal := by
    simpa [hP_sub] using (inferInstance : H.Normal)
  -- Step 8: Normal Sylow subgroups are characteristic.
  have hP_char : P.Characteristic :=
    Sylow.characteristic_of_normal (G := G) P hP_normal
  -- Step 9: Translate the characteristic property from `P` back to `H`.
  simpa [hP_sub] using hP_char
