import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that for all $n>1$ that $\mathbb{Z}/n\mathbb{Z}$ is not a group under multiplication of residue classes.
-/

/-Informal Proof

Note that since $n>1, \overline{1} \neq \overline{0}$. Now suppose $\mathbb{Z} /(n)$ contains a multiplicative identity element $\bar{e}$. Then in particular,
$$
\bar{e} \cdot \overline{1}=\overline{1}
$$
so that $\bar{e}=\overline{1}$. Note, however, that
$$
\overline{0} \cdot \bar{k}=\overline{0}
$$
for all k, so that $\overline{0}$ does not have a multiplicative inverse. Hence $\mathbb{Z} /(n)$ is not a group under multiplication.
-/

theorem Dummit_Foote_exercise_1_1_5 (n : ℕ) (hn : 1 < n) :
  IsEmpty (Group (ZMod n)) := by
  sorry

/-
Explanation for invalid statement:
Step 1: The formal claim above states that there is no multiplicative group structure on `ZMod n`.
Step 2: However, we can reuse the additive structure of `ZMod n` to build a multiplicative group
        structure by declaring the group multiplication to be addition, the identity to be `0`
        and the inverse to be negation.
Step 3: This construction works for every `n`, so the type `Group (ZMod n)` is in fact inhabited.
Step 4: Consequently the original statement is false; we keep it with `sorry` as required and
        now supply a proof of its logical negation.
-/

theorem Dummit_Foote_exercise_1_1_5_neg (n : ℕ) (hn : 1 < n) :
  ¬ IsEmpty (Group (ZMod n)) := by
  classical
  -- Step 0: Record the side condition (unused later because the construction works for all `n`).
  have _ : 1 < n := hn
  -- Step 1: Introduce the assumption that the type of group structures is empty.
  intro hEmpty
  -- Step 2: Prepare auxiliary multiplicative data by reusing additive operations of `ZMod n`.
  -- Step 2.1: Use addition as a temporary multiplication.
  let _ : Mul (ZMod n) := ⟨fun a b => a + b⟩
  -- Step 2.2: Use zero as the temporary multiplicative identity.
  let _ : One (ZMod n) := ⟨0⟩
  -- Step 2.3: Use negation as the temporary inverse operation.
  let _ : Inv (ZMod n) := ⟨fun a => -a⟩
  -- Step 3: Verify associativity for the temporary multiplication.
  have hAssoc :
      ∀ a b c : ZMod n, (a * b) * c = a * (b * c) := by
    -- Step 3.1: Rewrite back to addition and invoke associativity of addition.
    intro a b c
    change (a + b) + c = a + (b + c)
    simp [add_assoc]
  -- Step 4: Verify the left identity axiom.
  have hOneMul : ∀ a : ZMod n, (1 : ZMod n) * a = a := by
    -- Step 4.1: Simplify using the temporary identity and additive identity law.
    intro a
    change (0 : ZMod n) + a = a
    simp
  -- Step 5: Verify the left inverse axiom.
  have hInvMul : ∀ a : ZMod n, a⁻¹ * a = (1 : ZMod n) := by
    -- Step 5.1: Simplify using negation, addition and the additive inverse cancellation law.
    intro a
    change (-a) + a = (0 : ZMod n)
    simp
  -- Step 6: Assemble the temporary data into an actual group structure.
  let candidate : Group (ZMod n) :=
    Group.ofLeftAxioms hAssoc hOneMul hInvMul
  -- Step 7: Contradict the emptiness assumption by providing the candidate structure.
  exact hEmpty.elim candidate

/-
Corrected statement (informal):
Step 1: When `n > 1`, the residue class `0` in `ZMod n` cannot have a multiplicative inverse.
Step 2: Therefore the standard multiplicative structure on `ZMod n` is not a group, because
        at least one element fails to have an inverse.
-/

theorem Dummit_Foote_exercise_1_1_5_corrected (n : ℕ) (hn : 1 < n) :
  ¬ (∀ x : ZMod n, ∃ y : ZMod n, x * y = (1 : ZMod n) ∧ y * x = 1) := by
  classical
  -- Step 1: Register the inequality `1 < n` as a typeclass fact so that `ZMod n` is nontrivial.
  haveI : Fact (1 < n) := ⟨hn⟩
  -- Step 2: Work by contradiction, assuming every element possesses a two-sided inverse.
  intro hAllInv
  -- Step 3: Instantiate the assumption with the residue class `0`.
  obtain ⟨k, hk⟩ := hAllInv 0
  -- Step 4: Extract the left inverse claim for `0` and simplify it.
  -- Step 4.1: The product `0 * k` simplifies to `0`, contradicting `hk.1`.
  have hZeroMul : (0 : ZMod n) * k = 0 := zero_mul k
  -- Step 4.2: Combine the simplification with `hk.1` to deduce `0 = 1`.
  have hContr : (0 : ZMod n) = 1 := by
    simpa [hZeroMul] using hk.1
  -- Step 5: Derive the final contradiction from the nontriviality of `ZMod n`.
  have : (0 : ZMod n) ≠ 1 := zero_ne_one
  exact this hContr
