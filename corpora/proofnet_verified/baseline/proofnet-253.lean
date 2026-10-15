import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that the polynomial $x^{2}-\sqrt{2}$ is irreducible over $\mathbb{Z}[\sqrt{2}]$. You may assume that $\mathbb{Z}[\sqrt{2}]$ is a U.F.D.
-/

/-Informal Proof

$Z[\sqrt{2}]$ is an Euclidean domain, and so a unique factorization domain.
We have to prove $p(x)=x^2-\sqrt{2}$ irreducible.
Suppose to the contrary.
if $p(x)$ is reducible then it must have root.
Let $a+b \sqrt{2}$ be a root of $x^2-\sqrt{2}$.
Now we have
$$
a^2+2 b^2+2 a b \sqrt{2}=\sqrt{2}
$$
By comparing the coefficients we get $2 a b=1$ for some pair of integers $a$ and $b$, a contradiction.
So $p(x)$ is irredicible over $Z[\sqrt{2}]$.
-/

theorem Dummit_Foote_exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  classical
  -- Step 0: Build an explicit `IsDomain` structure using the injective embedding into `ℝ`.
  have h_nat_sq_ne_two : ∀ m : ℕ, m * m ≠ 2 := by
    -- Step 0.1: Run a case split on the three possible sizes of `m`.
    intro m
    cases' m with m
    · simp
    cases' m with m
    · simp
    -- Step 0.1.1: In the remaining case `m ≥ 2`, any square is at least `4`.
    intro hsq
    have hge :
        (4 : ℕ) ≤ Nat.succ (Nat.succ m) * Nat.succ (Nat.succ m) := by
      have htwo : 2 ≤ Nat.succ (Nat.succ m) :=
        Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
      exact Nat.mul_le_mul htwo htwo
    simp [hsq] at hge
  have h_no_sq : ∀ n : ℤ, (2 : ℤ) ≠ n * n := by
    -- Step 0.2: Reduce the integer statement to the natural one via `natAbs`.
    intro n hn
    have : n.natAbs * n.natAbs = 2 := by
      -- Cast the equation `n * n = 2` back to naturals using `natAbs`.
      apply Int.ofNat.inj
      simpa [Int.natAbs_mul_self] using hn.symm
    exact h_nat_sq_ne_two n.natAbs this
  have h_inj :
      Function.Injective
        (Zsqrtd.toReal (d := 2) (by decide : (0 : ℤ) ≤ 2)) :=
    Zsqrtd.toReal_injective (h0d := by decide) (hd := h_no_sq)
  haveI : IsDomain (Zsqrtd 2) :=
    h_inj.isDomain (Zsqrtd.toReal (d := 2) (by decide : (0 : ℤ) ≤ 2))
  -- Step 1: Collect the basic invariants of the quadratic polynomial.
  have h_monic :
      Monic (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
    -- Step 1.1: Invoke the standard lemma for `X^n - C a` with `n = 2`.
    simpa using
      (Polynomial.monic_X_pow_sub_C (R := Zsqrtd 2) (a := Zsqrtd.sqrtd)
        (n := 2) (by decide : (2 : ℕ) ≠ 0))
  -- Step 1.2: Record the exact natural degree, which will sit inside `[1, 3]`.
  have h_natDeg :
      (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)).natDegree = 2 := by
    simp
  -- Step 1.3: Translate this numerical information to the inequalities required later on.
  have h_deg_lower :
      2 ≤ (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)).natDegree := by
    -- Step 1.3.1: The equality `natDegree = 2` trivially implies the lower bound.
    simp [h_natDeg]
  have h_deg_upper :
      (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)).natDegree ≤ 3 := by
    -- Step 1.3.2: Likewise, the upper bound follows immediately from the computed degree.
    simp [h_natDeg]
  -- Step 1.4: Note explicitly that the polynomial is nonzero so that the root lemmas apply cleanly.
  have h_ne_zero :
      (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) ≠ 0 :=
    h_monic.ne_zero
  -- Step 2: Rule out the existence of any root inside `ℤ[√2]`.
  have h_no_root :
      ∀ z : Zsqrtd 2,
        ¬ IsRoot (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) z := by
    -- Step 2.1: Fix an arbitrary element and expand the root condition.
    intro z hz
    -- Step 2.1.1: Interpret `IsRoot` as the explicit equality `z² = √2`.
    have hz_sq : z * z = Zsqrtd.sqrtd := by
      -- Step 2.1.1.1: Evaluating the polynomial at `z` simply produces `z² - √2`.
      simpa [IsRoot, pow_two, sub_eq_zero] using hz
    -- Step 2.2: Inspect the imaginary component of this equality to obtain the parity obstruction.
    have h_sum :
        z.re * z.im + z.re * z.im = 1 := by
      -- Step 2.2.1: Taking imaginary parts gives the displayed symmetric sum.
      simpa [Zsqrtd.im_mul, Zsqrtd.im_sqrtd, add_comm, add_left_comm, add_assoc, mul_comm]
        using congrArg Zsqrtd.im hz_sq
    -- Step 2.3: Conclude that `1` is even, contradicting the basic fact `¬Even 1`.
    have h_even : Even (1 : ℤ) := ⟨z.re * z.im, h_sum.symm⟩
    exact (Int.not_even_one : ¬ Even (1 : ℤ)) h_even
  -- Step 3: Convert the “no roots” information into irreducibility through the degree-≤3 criterion.
  have h_roots_zero :
      (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)).roots = 0 := by
    -- Step 3.1: A multiset is empty if and only if no element can lie inside it.
    apply Multiset.eq_zero_of_forall_notMem
    intro z hz
    -- Step 3.1.1: Membership in the root multiset is equivalent to the `IsRoot` predicate.
    have hz_root :
        IsRoot (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) z :=
      (Polynomial.mem_roots h_ne_zero).1 hz
    -- Step 3.1.2: Invoke Step 2 to reach the contradiction.
    exact h_no_root z hz_root
  -- Step 3.2: Apply the integral-domain version of the small-degree irreducibility test.
  refine
    (Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three
        (p := X ^ 2 - C Zsqrtd.sqrtd) h_monic h_deg_lower h_deg_upper).mpr
      h_roots_zero
