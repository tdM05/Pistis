import Mathlib

open Real
open scoped BigOperators



/-Informal Statement

Show that 1729 is the smallest positive integer expressible as the sum of two different integral cubes in two ways.
-/

/-Informal Proof

Let $n=a^3+b^3$, and suppose that $\operatorname{gcd}(a, b)=1$. If a prime $p \mid a^3+b^3$, then
$$
\left(a b^{-1}\right)^3 \equiv_p-1
$$
Thus $3 \mid \frac{p-1}{2}$, that is, $p \equiv_6 1$.
If we have $n=a^3+b^3=c^3+d^3$, then we can factor $n$ as
$$
\begin{aligned}
& n=(a+b)\left(a^2-a b+b^2\right) \\
& n=(c+d)\left(c^2-c d+d^2\right)
\end{aligned}
$$
Thus we need $n$ to have at least 3 distinct prime factors, and so the smallest taxicab number is on the form
$$
n=(6 k+1)(12 k+1)(18 k+1)
$$
-/

theorem Ireland_Rosen_exercise_18_4 : 1729 = sInf (fun (n : ℕ) => ∃ x y z w : ℤ,
  x^3 + y^3 = n ∧ z^3 + w^3 = n ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w) := by
  sorry



/-- The subset of natural numbers appearing in the original statement. -/
def taxicabSet : Set ℕ :=
  fun n => ∃ x y z w : ℤ,
    x ^ 3 + y ^ 3 = n ∧ z ^ 3 + w ^ 3 = n ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w

lemma zero_mem_taxicabSet : 0 ∈ taxicabSet := by
  -- Step 1: Introduce explicit witnesses certifying the membership of `0`.
  refine ⟨1, -1, 2, -2, ?_⟩
  -- Step 2: Record the two cube-sum equalities for the chosen integers.
  have h_left : (1 : ℤ) ^ 3 + (-1 : ℤ) ^ 3 = 0 := by
    -- Step 2.1: Evaluate each cube numerically.
    norm_num
  have h_right : (2 : ℤ) ^ 3 + (-2 : ℤ) ^ 3 = 0 := by
    -- Step 2.2: Evaluate each cube numerically.
    norm_num
  -- Step 3: Assemble the equalities together with the distinctness constraints.
  refine ⟨h_left, ?_⟩
  refine ⟨h_right, ?_⟩
  -- Step 3.1: Finish by discharging the inequality side-conditions.
  exact ⟨by decide, ⟨by decide, ⟨by decide, by decide⟩⟩⟩

lemma sInf_taxicabSet_eq_zero : sInf taxicabSet = 0 := by
  -- Step 1: Note that `0` belongs to the set via the previous lemma.
  have h_mem : 0 ∈ taxicabSet := zero_mem_taxicabSet
  -- Step 2: Use the minimality of `Nat.sInf` to bound the infimum from above.
  have h_le : sInf taxicabSet ≤ 0 := Nat.sInf_le h_mem
  -- Step 3: Use nonnegativity of natural numbers for the reverse inequality.
  have h_nonneg : 0 ≤ sInf taxicabSet := Nat.zero_le _
  -- Step 4: Combine both inequalities into the desired equality.
  exact Nat.le_antisymm h_le h_nonneg

/-!
Explanation: The original formalisation allows arbitrary integers, so `0` already
has two distinct decompositions as a sum of cubes, e.g. `0 = 1^3 + (-1)^3 =
2^3 + (-2)^3`. Consequently `0` is contained in the set whose infimum is taken,
so the infimum is `0`, not `1729`.
-/

theorem Ireland_Rosen_exercise_18_4_neg :
    1729 ≠ sInf taxicabSet := by
  -- Step 1: Replace the infimum with the explicit value computed above.
  have h_sInf : sInf taxicabSet = 0 := sInf_taxicabSet_eq_zero
  -- Step 2: Reduce to the obvious numerical inequality.
  have h_num : 1729 ≠ (0 : ℕ) := by
    -- Step 2.1: Let the decision procedure establish the inequality.
    decide
  -- Step 3: Substitute the computed infimum and conclude.
  simp [h_sInf]

/-
Corrected statement: If we restrict to positive integers and only allow
summands between `1` and `12` (which suffices for sums strictly below `1729`),
then `1729` becomes the least positive integer admitting two disjoint pairs of
positive cubes with the same sum.
-/

def correctedPredicate (n : ℕ) : Prop :=
  0 < n ∧
    ∃ x y z w : ℕ,
      0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < w ∧
        x ^ 3 + y ^ 3 = n ∧
        z ^ 3 + w ^ 3 = n ∧
        x ≠ y ∧ w ≠ z ∧
        x ≠ z ∧ x ≠ w ∧
        y ≠ z ∧ y ≠ w

def correctedSet : Set ℕ := fun n => correctedPredicate n

def positiveRange : Finset ℕ := Finset.Icc 1 12

def positivePairs : Finset (ℕ × ℕ) := positiveRange.product positiveRange

def pairSum (p : ℕ × ℕ) : ℕ := p.1 ^ 3 + p.2 ^ 3

def doublePairSums : Finset ℕ :=
  ((positivePairs.product positivePairs).filter fun q =>
      let p₁ := q.1
      let p₂ := q.2
      p₁.1 ≠ p₁.2 ∧ p₂.2 ≠ p₂.1 ∧
        p₁.1 ≠ p₂.1 ∧ p₁.1 ≠ p₂.2 ∧
        p₁.2 ≠ p₂.1 ∧ p₁.2 ≠ p₂.2 ∧
        pairSum p₁ = pairSum p₂).image fun q => pairSum q.1

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

lemma doublePairSums_eq_singleton : doublePairSums = ({1729} : Finset ℕ) := by
  -- Step 1: Exhaustively evaluate the finite search reflected in `doublePairSums`.
  decide

lemma le_twelve_of_sum_lt1729 {x y : ℕ} (_hx : 0 < x) (hy : 0 < y)
    (hxy : x ^ 3 + y ^ 3 < 1729) : x ≤ 12 := by
  -- Step 1: Argue by contradiction, assuming `x` exceeds `12`.
  by_contra hx_not_le
  -- Step 1.1: Turn the negated bound into the strict inequality `12 < x`.
  have hx_big : 12 < x := Nat.lt_of_not_ge hx_not_le
  -- Step 1.2: Convert the strict inequality into `13 ≤ x`.
  have hx_ge : 13 ≤ x := Nat.succ_le_of_lt hx_big
  -- Step 1.3: Obtain the lower bounds for the cubes of `x` and `y`.
  have hx_cube : 13 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hx_ge 3
  have hy_cube : 1 ^ 3 ≤ y ^ 3 := Nat.pow_le_pow_left (Nat.succ_le_of_lt hy) 3
  -- Step 1.4: Add the inequalities to bound the sum from below.
  have hsum : 13 ^ 3 + 1 ^ 3 ≤ x ^ 3 + y ^ 3 := Nat.add_le_add hx_cube hy_cube
  -- Step 1.5: Convert the numeric inequality into a contradiction.
  have hbig : 1729 ≤ x ^ 3 + y ^ 3 := by
    -- Step 1.5.1: Rewrite the explicit numeric bound.
    have hconst : 13 ^ 3 + 1 ^ 3 = 2198 := by norm_num
    -- Step 1.5.2: Combine the bounds to reach `1729 ≤ x ^ 3 + y ^ 3`.
    exact
      (Nat.le_trans (by decide : 1729 ≤ 2198) (by simpa [hconst] using hsum))
  -- Step 1.6: Contradict the original strict inequality.
  exact (Nat.not_lt_of_ge hbig) hxy

lemma mem_doublePairSums_of_correctedPredicate {n : ℕ}
    (hn : correctedPredicate n) (hn_lt : n < 1729) :
    n ∈ doublePairSums := by
  rcases hn with
    ⟨hn_pos, x, y, z, w, hx_pos, hy_pos, hz_pos, hw_pos, hx_sum, hz_sum, hxy, hwz, hxz, hxw, hyz, hyw⟩
  have hxy_lt : x ^ 3 + y ^ 3 < 1729 := by simpa [hx_sum] using hn_lt
  have hzw_lt : z ^ 3 + w ^ 3 < 1729 := by simpa [hz_sum] using hn_lt
  have hx_le : x ≤ 12 := le_twelve_of_sum_lt1729 hx_pos hy_pos hxy_lt
  have hy_le : y ≤ 12 := by
    have hy_lt : y ^ 3 + x ^ 3 < 1729 := by simpa [Nat.add_comm] using hxy_lt
    simpa [Nat.add_comm] using le_twelve_of_sum_lt1729 hy_pos hx_pos hy_lt
  have hz_le : z ≤ 12 := by
    have hz_lt : z ^ 3 + w ^ 3 < 1729 := hzw_lt
    simpa using le_twelve_of_sum_lt1729 hz_pos hw_pos hz_lt
  have hw_le : w ≤ 12 := by
    have hw_lt : w ^ 3 + z ^ 3 < 1729 := by simpa [Nat.add_comm] using hzw_lt
    simpa [Nat.add_comm] using le_twelve_of_sum_lt1729 hw_pos hz_pos hw_lt
  have hx_mem : x ∈ positiveRange :=
    Finset.mem_Icc.mpr ⟨(Nat.succ_le_iff).mpr hx_pos, hx_le⟩
  have hy_mem : y ∈ positiveRange :=
    Finset.mem_Icc.mpr ⟨(Nat.succ_le_iff).mpr hy_pos, hy_le⟩
  have hz_mem : z ∈ positiveRange :=
    Finset.mem_Icc.mpr ⟨(Nat.succ_le_iff).mpr hz_pos, hz_le⟩
  have hw_mem : w ∈ positiveRange :=
    Finset.mem_Icc.mpr ⟨(Nat.succ_le_iff).mpr hw_pos, hw_le⟩
  have hp_prod :
      ((x, y), (z, w)) ∈ positivePairs.product positivePairs :=
    Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hx_mem, hy_mem⟩,
       Finset.mem_product.mpr ⟨hz_mem, hw_mem⟩⟩
  have hp_filter :
      ((x, y), (z, w)) ∈
          (positivePairs.product positivePairs).filter fun q =>
            let p₁ := q.1
            let p₂ := q.2
            p₁.1 ≠ p₁.2 ∧ p₂.2 ≠ p₂.1 ∧
              p₁.1 ≠ p₂.1 ∧ p₁.1 ≠ p₂.2 ∧
              p₁.2 ≠ p₂.1 ∧ p₁.2 ≠ p₂.2 ∧
              pairSum p₁ = pairSum p₂ := by
    refine Finset.mem_filter.mpr ⟨hp_prod, ?_⟩
    exact ⟨hxy, hwz, hxz, hxw, hyz, hyw, by simp [pairSum, hx_sum, hz_sum]⟩
  refine Finset.mem_image.mpr ?_
  exact ⟨((x, y), (z, w)), hp_filter, by simp [pairSum, hx_sum]⟩

lemma correctedPredicate_small {n : ℕ} (hn_lt : n < 1729) :
    ¬ correctedPredicate n := by
  -- Step 1: Assume the predicate holds and derive a contradiction.
  intro hn
  -- Step 2: Convert the predicate into membership of the finite classification set.
  have h_mem : n ∈ doublePairSums := mem_doublePairSums_of_correctedPredicate hn hn_lt
  -- Step 3: Use the explicit classification to pin down the only possible value.
  have h_singleton : doublePairSums = ({1729} : Finset ℕ) := doublePairSums_eq_singleton
  have h_eq : n = 1729 := by
    -- Step 3.1: Reduce the membership statement to the singleton case.
    have : n ∈ ({1729} : Finset ℕ) := by simpa [h_singleton] using h_mem
    exact Finset.mem_singleton.mp this
  -- Step 4: Contradict the strict inequality using the established equality.
  simp [h_eq] at hn_lt

lemma correctedPredicate_1729 : correctedPredicate 1729 := by
  refine ⟨by decide, 1, 12, 9, 10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide


theorem Ireland_Rosen_exercise_18_4_corrected :
    1729 = sInf (fun n => 0 < n ∧
      ∃ x y z w : ℕ,
        0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < w ∧
          x ^ 3 + y ^ 3 = n ∧
          z ^ 3 + w ^ 3 = n ∧
            x ≠ y ∧ w ≠ z ∧
            x ≠ z ∧ x ≠ w ∧
            y ≠ z ∧ y ≠ w) := by
  -- Step 1: Observe that the corrected set is inhabited.
  have h_mem : correctedPredicate 1729 := correctedPredicate_1729
  -- Step 1.1: Record the resulting membership explicitly.
  have h_in : 1729 ∈ correctedSet := h_mem
  -- Step 2: Bound the infimum from above using the membership of `1729`.
  have h_le : sInf correctedSet ≤ 1729 := Nat.sInf_le h_in
  -- Step 3: Use the minimality of the infimum to obtain the reverse inequality.
  have h_nonempty : correctedSet.Nonempty := ⟨1729, h_mem⟩
  have h_inf_mem : correctedPredicate (sInf correctedSet) := Nat.sInf_mem h_nonempty
  have h_not_lt : ¬ sInf correctedSet < 1729 := fun h_lt =>
    (correctedPredicate_small h_lt) h_inf_mem
  have h_ge : 1729 ≤ sInf correctedSet := le_of_not_gt h_not_lt
  -- Step 4: Combine the two inequalities into the desired equality.
  exact le_antisymm h_ge h_le
