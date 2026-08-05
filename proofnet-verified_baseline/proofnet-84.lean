import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Show that there is an infinite number of solutions to $x^2 = -1$ in the quaternions.
-/

/-Informal Proof

Let $x=a i+b j+c k$ then
$$
x^2=(a i+b j+c k)(a i+b j+c k)=-a^2-b^2-c^2=-1
$$
This gives $a^2+b^2+c^2=1$ which has infinitely many solutions for $-1<a, b, c<1$.
-/

theorem Herstein_exercise_4_1_19 : Infinite {x : Quaternion ℝ | x^2 = -1} := by
  -- Step 1: Parametrize solutions using angles on the unit circle inside the imaginary `i-j` plane.
  classical
  let g : ℝ → Quaternion ℝ := fun θ => ⟨0, Real.cos θ, Real.sin θ, 0⟩
  -- Step 2: Show that every `g θ` squares to `-1`.
  have hg_sq : ∀ θ : ℝ, (g θ) ^ 2 = (-1 : Quaternion ℝ) := by
    -- Step 2.1: Fix an arbitrary angle `θ` and recall the fundamental trigonometric identity.
    intro θ
    have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    -- Step 2.2: Compute `g θ * g θ` componentwise to deduce the desired equality.
    have hmul : g θ * g θ = (-1 : Quaternion ℝ) := by
      ext
      · have hcalc' :
            (g θ * g θ).re =
              -(Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ) := by
          simp [g, Quaternion.re_mul, sub_eq_add_neg, add_comm]
        have hcalc :
            (g θ * g θ).re =
              -(Real.cos θ ^ 2 + Real.sin θ ^ 2) := by
          simpa [pow_two, add_comm] using hcalc'
        simpa [htrig] using hcalc
      · simp [g, Quaternion.imI_mul, mul_comm]
      · simp [g, Quaternion.imJ_mul, mul_comm]
      · simp [g, Quaternion.imK_mul, mul_comm]
    -- Step 2.3: Convert the product identity into the statement about squares.
    simpa [pow_two] using hmul
  -- Step 3: Restrict to the open interval where `sin` is strictly monotone to obtain injectivity.
  let I : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
  let gI : I → Quaternion ℝ := fun θ => g θ.1
  -- Step 3.1: Record that every parameter in `I` lands in the solution set.
  have hg_mem : ∀ θ : I, gI θ ∈ {x : Quaternion ℝ | x ^ 2 = -1} := by
    intro θ
    simp [gI, g, hg_sq θ.1]
  -- Step 3.2: Prove that `g` is injective on the chosen interval.
  have hg_inj : Function.Injective gI := by
    intro θ₁ θ₂ h
    apply Subtype.ext
    -- Step 3.2.1: Translate equality of quaternions to equality of their `sin` components.
    have hsin : Real.sin θ₁.1 = Real.sin θ₂.1 := by
      simpa [gI, g] using congrArg (fun q => q.imJ) h
    -- Step 3.2.2: Use the strict monotonicity of `sin` on `[-π/2, π/2]` to conclude `θ₁ = θ₂`.
    have hθ₁ :
        θ₁.1 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨le_of_lt θ₁.property.1, le_of_lt θ₁.property.2⟩
    have hθ₂ :
        θ₂.1 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨le_of_lt θ₂.property.1, le_of_lt θ₂.property.2⟩
    exact Real.injOn_sin hθ₁ hθ₂ hsin
  -- Step 4: Observe that the domain interval is infinite, hence so is its subtype.
  have hpos : 0 < Real.pi / 2 := by
    simpa using half_pos Real.pi_pos
  have hlt : -(Real.pi / 2) < Real.pi / 2 := by simpa using neg_lt_self hpos
  have hI_type_inf : Infinite (Subtype I) := Set.Ioo.infinite hlt
  -- Step 5: Apply the injective image lemma to obtain an infinite subset of solutions.
  have hsubset_inf :
      Set.Infinite {x : Quaternion ℝ | x ^ 2 = -1} := by
    -- Step 5.1: Equip `I` with its infinitude and invoke the general lemma.
    have _inst : Infinite I := hI_type_inf
    exact
      Set.infinite_of_injective_forall_mem
        (fun {θ₁ θ₂} h => hg_inj h)
        (fun θ => hg_mem θ)
  -- Step 6: Convert the set-level infinitude into the desired subtype statement.
  exact (Set.infinite_coe_iff).mpr hsubset_inf
