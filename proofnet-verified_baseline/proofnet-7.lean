import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Prove that two elements $a, b$ of a group generate the same subgroup as $b a b^2, b a b^3$.
-/

/-Informal Proof

Let $H = \langle bab^2, bab^3\rangle$. It is clear that $H\subset \langle a, b\rangle$. Note that $(bab^2)^{-1}(bab^3)=b$, therefore $b\in H$. This then implies that $b^{-1}(bab^2)b^{-2}=a\in H$. Thus $\langle a, b\rangle\subset H$.
-/

/-!
Formal proof with explicit step-by-step commentary begins below.
-/

theorem Artin_exercise_6_8_1 {G : Type*} [Group G]
  (a b : G) : closure ({a, b} : Set G) = Subgroup.closure {b*a*b^2, b*a*b^3} := by
  classical
  -- Step 1: Prove the subgroup equality by establishing mutual inclusions.
  refine le_antisymm ?left_to_right ?right_to_left
  -- Step 2: Show `closure {a, b}` is contained in `Subgroup.closure {b * a * b ^ 2, b * a * b ^ 3}`.
  · -- Step 2.1: Introduce the target subgroup and record that the generators belong to it.
    have hb :
        b ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) := by
      -- Step 2.1.1: The generator `b * a * b ^ 2` lies in the closure by construction.
      have h_bab2 :
          b * a * b ^ 2 ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
        Subgroup.subset_closure (by
          -- Step 2.1.1.1: Simplify membership in the generating set.
          simp [Set.mem_insert_iff, Set.mem_singleton_iff])
      -- Step 2.1.2: The generator `b * a * b ^ 3` lies in the closure by construction.
      have h_bab3 :
          b * a * b ^ 3 ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
        Subgroup.subset_closure (by
          -- Step 2.1.2.1: Simplify membership in the generating set.
          simp [Set.mem_insert_iff, Set.mem_singleton_iff])
      -- Step 2.1.3: Combine the generators to express `b` as their product.
      have hb_prod :
          (b * a * b ^ 2)⁻¹ * (b * a * b ^ 3)
            ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ h_bab2) h_bab3
      -- Step 2.1.4: Simplify the product to show it equals `b`.
      simpa [pow_two, pow_succ, mul_assoc] using hb_prod
    -- Step 2.2: Use the universal property of the closure to send each generator into the target subgroup.
    refine (closure_le (K := Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G))).2 ?_
    intro x hx
    -- Step 2.2.1: Reduce membership in `{a, b}` to two explicit cases.
    have hx' : x = a ∨ x = b := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff]
    -- Step 2.2.2: Discharge each case separately.
    cases hx' with
    | inl h =>
        -- Step 2.2.2.1: Interpret the goal using the case hypothesis `h : x = a`.
        -- Step 2.2.2.2: Prepare useful elements already known to be in the target subgroup.
        have hb_inv :
            b⁻¹ ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
          Subgroup.inv_mem _ hb
        have h_bab2 :
            b * a * b ^ 2 ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
          Subgroup.subset_closure (by
            -- Step 2.2.2.2.1: Again unpack membership in the generating set.
            simp [Set.mem_insert_iff, Set.mem_singleton_iff])
        -- Step 2.2.2.3: Build the product `b⁻¹ * (b * a * b ^ 2)`.
        have h_prefactor :
            b⁻¹ * (b * a * b ^ 2)
              ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
          Subgroup.mul_mem _ hb_inv h_bab2
        -- Step 2.2.2.4: Record that `b⁻¹ * b⁻¹` is in the subgroup.
        have hb_inv_sq :
            b⁻¹ * b⁻¹
              ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
          Subgroup.mul_mem _ hb_inv hb_inv
        -- Step 2.2.2.5: Combine everything to obtain a representative equal to `a`.
        have ha_mem :
            (b⁻¹ * (b * a * b ^ 2)) * (b⁻¹ * b⁻¹)
              ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
          Subgroup.mul_mem _ h_prefactor hb_inv_sq
        -- Step 2.2.2.6: Simplify the representative to conclude that `a` is in the subgroup.
        have ha :
            a ∈ Subgroup.closure ({b * a * b ^ 2, b * a * b ^ 3} : Set G) :=
          by simpa [pow_two, mul_assoc] using ha_mem
        -- Step 2.2.2.7: Transport the membership back to `x` using `h`.
        simpa [h] using ha
    | inr h =>
        -- Step 2.2.2.8: Conclude immediately using the established membership of `b`.
        simpa [h] using hb
  -- Step 3: Show `Subgroup.closure {b * a * b ^ 2, b * a * b ^ 3}` is contained in `closure {a, b}`.
  · -- Step 3.1: Record the basic elements of `closure {a, b}` that will be reused.
    have hb :
        b ∈ closure ({a, b} : Set G) :=
      Subgroup.subset_closure (by
        -- Step 3.1.1: Simplify membership of `b` in `{a, b}`.
        simp [Set.mem_insert_iff, Set.mem_singleton_iff])
    have ha :
        a ∈ closure ({a, b} : Set G) :=
      Subgroup.subset_closure (by
        -- Step 3.1.2: Simplify membership of `a` in `{a, b}`.
        simp [Set.mem_insert_iff, Set.mem_singleton_iff])
    -- Step 3.1.3: Higher powers of `b` also belong because the closure is a subgroup.
    have hb_two :
        b ^ 2 ∈ closure ({a, b} : Set G) :=
      Subgroup.pow_mem _ hb 2
    have hb_three :
        b ^ 3 ∈ closure ({a, b} : Set G) :=
      Subgroup.pow_mem _ hb 3
    -- Step 3.2: Use the universal property of the closure to absorb the generators on the right.
    refine (closure_le (K := closure ({a, b} : Set G))).2 ?_
    intro x hx
    -- Step 3.2.1: Reduce membership in `{b * a * b ^ 2, b * a * b ^ 3}` to explicit cases.
    have hx' : x = b * a * b ^ 2 ∨ x = b * a * b ^ 3 := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff]
    -- Step 3.2.2: Treat both generators separately.
    cases hx' with
    | inl h =>
        -- Step 3.2.2.1: Interpret the goal using `h : x = b * a * b ^ 2`.
        -- Step 3.2.2.2: Combine `b`, `a`, and `b ^ 2` to show the product lies in the closure.
        have h_mul :
            b * a ∈ closure ({a, b} : Set G) :=
          Subgroup.mul_mem _ hb ha
        have h_target :
            (b * a) * b ^ 2 ∈ closure ({a, b} : Set G) :=
          Subgroup.mul_mem _ h_mul hb_two
        -- Step 3.2.2.3: Simplify back to the desired element and reinterpret via `h`.
        have h_bab2 :
            b * a * b ^ 2 ∈ closure ({a, b} : Set G) :=
          by simpa [mul_assoc] using h_target
        simpa [h] using h_bab2
    | inr h =>
        -- Step 3.2.2.4: Interpret the goal using `h : x = b * a * b ^ 3`.
        -- Step 3.2.2.5: Combine the same base elements with `b ^ 3`.
        have h_mul :
            b * a ∈ closure ({a, b} : Set G) :=
          Subgroup.mul_mem _ hb ha
        have h_target :
            (b * a) * b ^ 3 ∈ closure ({a, b} : Set G) :=
          Subgroup.mul_mem _ h_mul hb_three
        -- Step 3.2.2.6: Simplify back to the desired element and reinterpret via `h`.
        have h_bab3 :
            b * a * b ^ 3 ∈ closure ({a, b} : Set G) :=
          by simpa [mul_assoc] using h_target
        simpa [h] using h_bab3
