import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Show that a group of order 5 must be abelian.
-/

/-Informal Proof

Suppose $G$ is a group of order 5 which is not abelian. Then there exist two non-identity elements $a, b \in G$ such that $a * b \neq$ $b * a$. Further we see that $G$ must equal $\{e, a, b, a * b, b * a\}$. To see why $a * b$ must be distinct from all the others, not that if $a *$ $b=e$, then $a$ and $b$ are inverses and hence $a * b=b * a$.
Contradiction. If $a * b=a$ (or $=b$ ), then $b=e$ (or $a=e$ ) and $e$ commutes with everything. Contradiction. We know by supposition that $a * b \neq b * a$. Hence all the elements $\{e, a, b, a * b, b * a\}$ are distinct.

Now consider $a^2$. It can't equal $a$ as then $a=e$ and it can't equal $a * b$ or $b * a$ as then $b=a$. Hence either $a^2=e$ or $a^2=b$.
Now consider $a * b * a$. It can't equal $a$ as then $b * a=e$ and hence $a * b=b * a$. Similarly it can't equal $b$. It also can't equal $a * b$ or $b * a$ as then $a=e$. Hence $a * b * a=e$.

So then we additionally see that $a^2 \neq e$ because then $a^2=e=$ $a * b * a$ and consequently $a=b * a$ (and hence $b=e$ ). So $a^2=b$. But then $a * b=a * a^2=a^2 * a=b * a$. Contradiction.
Hence starting with the assumption that there exists an order 5 abelian group $G$ leads to a contradiction. Thus there is no such group.
-/

theorem Herstein_exercise_2_1_21 (G : Type*) [Group G] [Fintype G]
  (hG : card G = 5) :
  ∀ a b : G, a*b = b*a := by
  -- Step 0: Enable classical logic to freely use choice-based arguments on finite types.
  classical
  -- Step 1: Introduce arbitrary elements `a` and `b` of the group.
  intro a b
  -- Step 2: Split into the cases where `a` is the identity and where it is not.
  by_cases ha : a = (1 : G)
  · -- Step 2.1: In the identity case, commutativity follows from the unit laws.
    -- Step 2.1.1: Rewrite the goal using `a = 1` and simplify with the group axioms.
    simp [ha]
  · -- Step 3: Work under the standing assumption `a ≠ 1`.
    -- Step 3.1: Record the primality of 5 for later divisibility arguments.
    have hp : Nat.Prime 5 := by decide
    -- Step 3.2: Define the centralizer subgroup of the singleton `{a}`.
    set H := Subgroup.centralizer ({a} : Set G) with hHdef
    -- Step 3.3: Observe that the identity element lies in the centralizer by definition.
    have hone_mem : (1 : G) ∈ H := by
      -- Step 3.3.1: Membership reduces to the identity commuting with `a`, which is automatic.
      simp [H]
    -- Step 3.4: Observe that `a` lies in its own centralizer.
    have ha_mem : a ∈ H := by
      -- Step 3.4.1: Membership reduces to `a` commuting with itself, which holds trivially.
      simp [H, Subgroup.mem_centralizer_singleton_iff]
    -- Step 3.5: Apply the subgroup index formula to relate the size of `H` to the whole group.
    have hindex_mul_nat : H.index * Nat.card H = 5 := by
      -- Step 3.5.1: Combine Lagrange's theorem with the assumption `|G| = 5`.
      have hindex_mul : H.index * Nat.card H = Nat.card G := Subgroup.index_mul_card H
      have hcardG : Nat.card G = 5 := by
        simp [Nat.card_eq_fintype_card, hG]
      exact hindex_mul.trans hcardG
    -- Step 3.6: Conclude that the index of `H` divides 5, hence is either 1 or 5.
    have hindex_dvd : H.index ∣ 5 :=
      ⟨Nat.card H, hindex_mul_nat.symm⟩
    -- Step 3.6.1: Enumerate the possible values of the index using the primality of 5.
    have hindex_cases : H.index = 1 ∨ H.index = 5 :=
      (Nat.dvd_prime hp).1 hindex_dvd
    -- Step 3.7: Rule out the possibility that the index equals 5 by deriving a contradiction.
    have hindex_eq_one : H.index = 1 := by
      -- Step 3.7.1: Analyse the two possible index values.
      rcases hindex_cases with hindex_one | hindex_five
      · -- Step 3.7.1.1: If the index is `1`, we are done.
        exact hindex_one
      · -- Step 3.7.1.2: Show that index `5` contradicts the assumption `a ≠ 1`.
        -- Step 3.7.1.2.1: Convert the index equation into a relation involving `Nat.card H`.
        have hmul_left : 5 * Nat.card H = 5 := by
          simpa [hindex_five, Nat.mul_comm] using hindex_mul_nat
        -- Step 3.7.1.2.2: Symmetrise the equality so that the common factor `5` is on the right.
        have hmul_right : Nat.card H * 5 = 1 * 5 := by
          calc
            Nat.card H * 5 = 5 * Nat.card H := by simp [Nat.mul_comm]
            _ = 5 := hmul_left
            _ = 1 * 5 := by simp
        -- Step 3.7.1.2.3: Cancel the non-zero factor `5` to deduce `Nat.card H = 1`.
        have hcard_eq_one : Nat.card H = 1 :=
          Nat.mul_right_cancel (by decide : 0 < 5) hmul_right
        -- Step 3.7.1.2.4: Express the singleton nature of `H` using `Fintype.card_eq_one`.
        have hcard_eq_one' : Fintype.card H = 1 := by
          simpa [Nat.card_eq_fintype_card] using hcard_eq_one
        obtain ⟨z, hz⟩ := Fintype.card_eq_one_iff.mp hcard_eq_one'
        -- Step 3.7.1.2.5: Show that `a` equals the identity by projecting the equality in `H`.
        have h_sub_eq :
            (⟨a, ha_mem⟩ : H) = ⟨1, hone_mem⟩ := by
          -- Step 3.7.1.2.5.1: Both elements equal the unique witness `z`, hence they are equal.
          have hz_a : (⟨a, ha_mem⟩ : H) = z := hz ⟨a, ha_mem⟩
          have hz_one : (⟨1, hone_mem⟩ : H) = z := hz ⟨1, hone_mem⟩
          exact hz_a.trans hz_one.symm
        -- Step 3.7.1.2.6: Forget the subtype to conclude `a = 1`, contradicting the assumption.
        have : a = (1 : G) := congrArg Subtype.val h_sub_eq
        have hcontr : False := ha this
        exact hcontr.elim
    -- Step 3.8: Convert the index statement into the equality `H = ⊤`.
    have hHtop : H = ⊤ := (Subgroup.index_eq_one).1 hindex_eq_one
    -- Step 3.9: Deduce that an arbitrary element `b` of `G` lies in `H`.
    have hb_mem : b ∈ H := by
      -- Step 3.9.1: Membership follows because the centralizer equals the top subgroup.
      rw [hHtop]; exact Subgroup.mem_top b
    -- Step 3.10: Unpack the definition of the centralizer to obtain the commuting relation.
    have hb_comm : b * a = a * b := by
      -- Step 3.10.1: Simplify the membership statement in the centralizer of `{a}`.
      simpa [H, hHdef, Subgroup.mem_centralizer_singleton_iff] using hb_mem
    -- Step 3.11: Symmetrise the equality to match the goal `a * b = b * a`.
    exact hb_comm.symm
