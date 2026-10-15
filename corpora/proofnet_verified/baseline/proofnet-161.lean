import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset Metric
open scoped BigOperators



/-Informal Statement

If $\Sigma a_{n}$ converges, and if $\left\{b_{n}\right\}$ is monotonic and bounded, prove that $\Sigma a_{n} b_{n}$ converges.
-/

/-Informal Proof

We shall show that the partial sums of this series form a Cauchy sequence, i.e., given $\varepsilon>0$ there exists $N$ such that $\left|\sum_{k=m+1}^n a_k b_k\right|\langle\varepsilon$ if $n\rangle$ $m \geq N$. To do this, let $S_n=\sum_{k=1}^n a_k\left(S_0=0\right)$, so that $a_k=S_k-S_{k-1}$ for $k=1,2, \ldots$ Let $M$ be an upper bound for both $\left|b_n\right|$ and $\left|S_n\right|$, and let $S=\sum a_n$ and $b=\lim b_n$. Choose $N$ so large that the following three inequalities hold for all $m>N$ and $n>N$ :
$$
\left|b_n S_n-b S\right|<\frac{\varepsilon}{3} ; \quad\left|b_m S_m-b S\right|<\frac{\varepsilon}{3} ; \quad\left|b_m-b_n\right|<\frac{\varepsilon}{3 M} .
$$
Then if $n>m>N$, we have, from the formula for summation by parts,
$$
\sum_{k=m+1}^n a_n b_n=b_n S_n-b_m S_m+\sum_{k=m}^{n-1}\left(b_k-b_{k+1}\right) S_k
$$
Our assumptions yield immediately that $\left|b_n S_n-b_m S_m\right|<\frac{2 \varepsilon}{3}$, and
$$
\left|\sum_{k=m}^{n-1}\left(b_k-b_{k+1}\right) S_k\right| \leq M \sum_{k=m}^{n-1}\left|b_k-b_{k+1}\right| .
$$
Since the sequence $\left\{b_n\right\}$ is monotonic, we have
$$
\sum_{k=m}^{n-1}\left|b_k-b_{k+1}\right|=\left|\sum_{k=m}^{n-1}\left(b_k-b_{k+1}\right)\right|=\left|b_m-b_n\right|<\frac{\varepsilon}{3 M},
$$
from which the desired inequality follows.
-/

theorem Rudin_exercise_3_8
  (a b : ℕ → ℝ)
  (h1 : ∃ y, (Tendsto (λ n => (∑ i ∈ (range n), a i)) atTop (𝓝 y)))
  (h2 : Monotone b)
  (h3 : Bornology.IsBounded (Set.range b)) :
  ∃ y, Tendsto (λ n => (∑ i ∈ (range n), (a i) * (b i))) atTop (𝓝 y) := by
  classical
  -- Step 1: name the partial sums of `a` so we can refer to them easily.
  --         We also extract the limit `A` of these partial sums from `h1`.
  rcases h1 with ⟨A, hA⟩
  set s : ℕ → ℝ := fun n => ∑ i ∈ range n, a i with hsdef
  have hs_tendsto : Tendsto s atTop (𝓝 A) := by
    -- Step 1.1: by definition of `s`, `hA` already states this tendsto fact.
    simpa [hsdef] using hA

  -- Step 2: the sequence of partial sums `s` is bounded because it converges.
  --         We extract an explicit bound `Ms` with |s n| ≤ Ms for every n.
  have hs_bdd : Bornology.IsBounded (Set.range s) :=
    Metric.isBounded_range_of_tendsto (u := s) hs_tendsto
  obtain ⟨Ms, hs_subset⟩ := hs_bdd.subset_closedBall 0
  have hs_abs : ∀ n, |s n| ≤ Ms := by
    -- Step 2.1: membership in the closed ball gives a distance bound.
    intro n
    have hs_mem : s n ∈ closedBall (0 : ℝ) Ms := hs_subset ⟨n, rfl⟩
    have hs_dist : dist (s n) 0 ≤ Ms := by
      -- `Metric.mem_closedBall` rewrites the membership condition as a distance inequality.
      simpa [Metric.mem_closedBall] using hs_mem
    -- Step 2.2: turn the distance bound into an absolute-value bound on ℝ.
    have hs_norm : ‖s n‖ ≤ Ms := by simpa [dist_eq_norm] using hs_dist
    simpa [Real.norm_eq_abs] using hs_norm

  -- Step 3: use monotonicity + boundedness of `b` to obtain its limit `bL`.
  have hb_bddAbove : BddAbove (Set.range b) :=
    ((isBounded_iff_bddBelow_bddAbove :
      Bornology.IsBounded (Set.range b) ↔ _)).1 h3 |>.2
  set bL := ⨆ i, b i
  have hb_tendsto : Tendsto b atTop (𝓝 bL) := tendsto_atTop_ciSup h2 hb_bddAbove

  -- Step 4: define the forward differences d n = b (n+1) - b n.
  set d : ℕ → ℝ := fun n => b (n + 1) - b n with hddef
  have hd_nonneg : ∀ n, 0 ≤ d n := by
    -- Step 4.1: monotonicity implies successive differences are nonnegative.
    intro n
    have hmono : b n ≤ b (n + 1) := h2 (Nat.le_succ n)
    have hge : b (n + 1) - b n ≥ 0 := sub_nonneg.mpr hmono
    exact hge

  -- Step 5: show the partial sums of d telescope to b n - b 0.
  have hd_telescope : ∀ n, (∑ i ∈ range n, d i) = b n - b 0 := by
    intro n
    induction' n with n ih
    · -- Step 5.1: base case n = 0.
      simp [hddef]
    · -- Step 5.2: inductive step n -> n+1 using telescoping.
      calc
        ∑ i ∈ range (n + 1), d i
            = (∑ i ∈ range n, d i) + d n := by simp [Finset.sum_range_succ]
        _ = (b n - b 0) + d n := by simp [ih]
        _ = (b n - b 0) + (b (n + 1) - b n) := by simp [hddef]
        _ = b (n + 1) - b 0 := by ring

  -- Step 6: identify the limit of the partial sums of `d` (they converge to `bL - b 0`).
  have hd_tendsto :
      Tendsto (fun n => ∑ i ∈ range n, d i) atTop (𝓝 (bL - b 0)) := by
    -- Step 6.1: rewrite using the telescope identity and the limit of b.
    have hsub := hb_tendsto.sub_const (b 0)
    simpa [hd_telescope] using hsub

  -- A small helper: the radius `Ms` coming from the closed ball is nonnegative.
  have Ms_nonneg : 0 ≤ Ms := by
    have h0 := hs_abs 0
    have : 0 ≤ |s 0| := abs_nonneg _
    nlinarith

  -- Step 7: define c n = d n * s (n+1); this is the weighted difference term.
  set c : ℕ → ℝ := fun n => d n * s (n + 1) with hcdef

  -- Step 8: bound the norm of c n by (Ms * d n), enabling later Cauchy estimates.
  have hc_bound : ∀ n, ‖c n‖ ≤ Ms * d n := by
    intro n
    have hd_abs : |d n| = d n := abs_of_nonneg (hd_nonneg n)
    have hs_norm : ‖s (n + 1)‖ ≤ Ms := by
      -- reuse the uniform bound on partial sums, shifted by 1.
      simpa [Real.norm_eq_abs] using hs_abs (n + 1)
    calc
      ‖c n‖ = |d n| * ‖s (n + 1)‖ := by
        -- Step 8.1: expand c and use the norm property on ℝ.
        simp [hcdef, Real.norm_eq_abs]
      _ ≤ d n * Ms := by
        -- Step 8.2: both factors are nonnegative, so we can multiply inequalities safely.
        have hd_nonneg' : 0 ≤ d n := hd_nonneg n
        nlinarith
      _ = Ms * d n := by ring

  -- Step 9: define the partial sums of c (needed for a Cauchy argument).
  set uc : ℕ → ℝ := fun n => ∑ i ∈ range n, c i with hucdef

  -- Step 10: establish the key inequality |uc n - uc m| ≤ Ms * |b n - b m|.
  have h_uc_bound : ∀ m n, |uc n - uc m| ≤ Ms * |b n - b m| := by
    classical
    -- First handle the case m ≤ n, then deduce the symmetric case.
    have hmono : ∀ m n, m ≤ n → |uc n - uc m| ≤ Ms * |b n - b m| := by
      intro m n hmn
      -- Rewrite the difference of partial sums of c as a sum over the tail starting at m.
      have htail : uc n - uc m = ∑ k ∈ Ico m n, c k := by
        -- `sum_Ico_eq_sub` expresses the tail as a difference of partial sums.
        have h := sum_Ico_eq_sub (f := fun k => c k) hmn
        -- h : ∑ k∈Ico m n, c k = ∑ k∈range n, c k - ∑ k∈range m, c k
        linarith [h]
      -- Bound the absolute value of this tail sum using the pointwise bound on `c`.
      calc
        |uc n - uc m| = ‖∑ k ∈ Ico m n, c k‖ := by simp [htail, Real.norm_eq_abs]
        _ ≤ ∑ k ∈ Ico m n, ‖c k‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Ico m n, Ms * d k := by
          -- apply the pointwise bound term-by-term
          refine sum_le_sum ?_
          intro k hk
          exact hc_bound k
        _ = Ms * (∑ k ∈ Ico m n, d k) := by simp [mul_sum]
        _ = Ms * (b n - b m) := by
          -- use the telescoping identity over the interval [m,n)
          have h := sum_Ico_eq_sub (f := fun k => d k) hmn
          -- h : ∑ k∈Ico m n, d k = ∑ k∈range n, d k - ∑ k∈range m, d k
          have h' : ∑ k ∈ Ico m n, d k = b n - b m := by
            calc
              ∑ k ∈ Ico m n, d k
                  = (∑ k ∈ range n, d k) - (∑ k ∈ range m, d k) := by
                    linarith [h]
              _ = (b n - b 0) - (b m - b 0) := by simp [hd_telescope]
              _ = b n - b m := by ring
          simp [h']
        _ ≤ Ms * |b n - b m| := by
          -- `b n - b m` is nonnegative (monotone b and m ≤ n), so drop absolute values safely.
          have hb_nonneg : 0 ≤ b n - b m := sub_nonneg.mpr (h2 hmn)
          have hb_abs : |b n - b m| = b n - b m := abs_of_nonneg hb_nonneg
          nlinarith
    intro m n
    -- use symmetry of the absolute value to handle the `n ≤ m` case by swapping.
    rcases le_total m n with hmn | hnm
    · exact hmono m n hmn
    · -- swap the roles of m and n and use symmetry of the absolute value
      have hswap := hmono n m hnm
      calc
        |uc n - uc m| = |uc m - uc n| := by simp [abs_sub_comm]
        _ ≤ Ms * |b m - b n| := hswap
        _ = Ms * |b n - b m| := by simp [abs_sub_comm]

  -- Step 11: the partial sums `uc` are Cauchy, hence convergent in ℝ (a complete space).
  have hb_cauchy : CauchySeq b := hb_tendsto.cauchySeq
  -- The comparison series g n = Ms * d n has Cauchy partial sums because d's partial sums converge.
  have hg_cauchy : CauchySeq (fun n => ∑ i ∈ range n, Ms * d i) := by
    have hg_tendsto :
        Tendsto (fun n => ∑ i ∈ range n, Ms * d i) atTop (𝓝 (Ms * (bL - b 0))) := by
      have := hd_tendsto
      -- multiply every partial sum by Ms
      have := this.const_mul Ms
      -- rewrite to factor Ms out of the sum notation
      simpa [mul_sum] using this
    exact hg_tendsto.cauchySeq
  have hc_cauchy : CauchySeq uc :=
    cauchySeq_range_of_norm_bounded (f := c) (g := fun i => Ms * d i) hg_cauchy
      (by intro i; simpa using hc_bound i)

  -- By completeness of ℝ, every Cauchy sequence converges; denote the limit by `C`.
  let C := limUnder atTop uc
  have hC : Tendsto uc atTop (𝓝 C) := hc_cauchy.tendsto_limUnder

  -- Step 10: relate the partial sums of the target series to the partial sums of c
  --          using the summation-by-parts (Abel) formula from mathlib.
  set t : ℕ → ℝ := fun n => ∑ i ∈ range n, a i * b i with htdef
  have ht_by_parts : ∀ n,
      t n = b (n - 1) * s n - ∑ i ∈ range (n - 1), c i := by
    intro n
    -- mathlib's `sum_range_by_parts` already encodes Abel's transformation.
    have h := Finset.sum_range_by_parts (f := b) (g := a) n
    -- First rewrite smul as multiplication and unfold the partial-sum notation `s`.
    have h' : ∑ i ∈ range n, b i * a i =
        b (n - 1) * s n - ∑ i ∈ range (n - 1), (b (i + 1) - b i) * s (i + 1) := by
      simpa [s, hsdef, t, htdef, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h
    -- Then replace the last sum with the definition of `c`.
    have h'' : ∑ i ∈ range n, b i * a i =
        b (n - 1) * s n - ∑ i ∈ range (n - 1), c i := by
      simpa [c, hcdef] using h'
    -- Finally commute the factors to match the statement of the lemma.
    simpa [t, htdef, mul_comm] using h''

  -- Step 11: specialize the by-parts formula to `n+1` to avoid predecessors.
  have ht_succ : ∀ n,
      t (n + 1) = b n * s (n + 1) - ∑ i ∈ range n, c i := by
    intro n
    -- Step 11.1: rewrite the general formula with n+1 and simplify (n+1)-1 to n.
    have h := ht_by_parts (n := n + 1)
    -- (n + 1) - 1 = n for naturals
    have hn : n + 1 - 1 = n := Nat.succ_sub_one n
    simpa [hn] using h

  -- Step 12: limits of the two pieces in the `ht_succ` formula.
  have hs_tendsto_succ : Tendsto (fun n => s (n + 1)) atTop (𝓝 A) :=
    (tendsto_add_atTop_iff_nat (f := s) (l := 𝓝 A) 1).2 hs_tendsto
  have h_mul : Tendsto (fun n => b n * s (n + 1)) atTop (𝓝 (bL * A)) :=
    hb_tendsto.mul hs_tendsto_succ
  -- C and its convergence were obtained in Step 11.

  -- Step 13: combine the two limits using the equality from Step 11.
  have ht_tendsto_aux :
      Tendsto (fun n => b n * s (n + 1) - ∑ i ∈ range n, c i)
        atTop (𝓝 (bL * A - C)) := by
    -- rewrite the auxiliary limit using the definition of `uc`
    have haux := h_mul.sub hC
    have h_eq : (fun n => b n * s (n + 1) - uc n)
        = fun n => b n * s (n + 1) - ∑ i ∈ range n, c i := by
      funext n; simp [uc]
    simpa [h_eq] using haux
  have ht_tendsto_succ :
      Tendsto (fun n => t (n + 1)) atTop (𝓝 (bL * A - C)) := by
    -- Step 13.1: replace the function using the pointwise equality `ht_succ`.
    have h_eq : (fun n => t (n + 1)) =ᶠ[atTop]
        (fun n => b n * s (n + 1) - ∑ i ∈ range n, c i) :=
      Eventually.of_forall (fun n => ht_succ n)
    exact (tendsto_congr' h_eq).mpr ht_tendsto_aux

  -- Step 14: shift back by 1; the limit of `t` matches the limit of `t ∘ succ`.
  have ht_tendsto_main : Tendsto t atTop (𝓝 (bL * A - C)) :=
    (tendsto_add_atTop_iff_nat (f := t) (l := 𝓝 (bL * A - C)) 1).1
      ht_tendsto_succ

  -- Step 15: package the result as the requested existence of a limit.
  exact ⟨bL * A - C, ht_tendsto_main⟩

/-
Problems with the original formalization:

The informal statement says `{b_n}` is "monotonic" — standard mathematical usage
covers both monotonically increasing and monotonically decreasing sequences. The
original Lean translation hard-codes `Monotone b`, which in Mathlib means only
*non-decreasing*. The decreasing case is dropped, so the original is strictly
weaker than Rudin's claim.

The corrected statement uses `Monotone b ∨ Antitone b`. The decreasing case
reduces to the existing theorem applied to `-b` (which is monotone and bounded),
then negate the resulting limit.
-/

/-- Corrected version of Rudin's exercise 3.8 (faithful to the informal statement):
"monotonic" covers both `Monotone` and `Antitone`. -/
theorem Rudin_exercise_3_8_corrected
    (a b : ℕ → ℝ)
    (h1 : ∃ y, Tendsto (fun n => ∑ i ∈ range n, a i) atTop (𝓝 y))
    (h2 : Monotone b ∨ Antitone b)
    (h3 : Bornology.IsBounded (Set.range b)) :
    ∃ y, Tendsto (fun n => ∑ i ∈ range n, a i * b i) atTop (𝓝 y) := by
  rcases h2 with hmono | hanti
  · -- Step 1: monotone case is the original theorem.
    exact Rudin_exercise_3_8 a b h1 hmono h3
  · -- Step 2: antitone case — apply the original theorem to `-b`, which is monotone.
    have hneg_mono : Monotone (fun n => -b n) :=
      fun i j hij => neg_le_neg (hanti hij)
    have hneg_bdd : Bornology.IsBounded (Set.range (fun n => -b n)) := by
      obtain ⟨M, hM⟩ := h3.subset_closedBall 0
      refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := M)).subset ?_
      rintro _ ⟨n, rfl⟩
      have hbn := hM ⟨n, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hbn ⊢
      rwa [norm_neg]
    -- Step 3: apply the original theorem to obtain the limit `y` of `∑ a i * (-b i)`.
    obtain ⟨y, hy⟩ := Rudin_exercise_3_8 a (fun n => -b n) h1 hneg_mono hneg_bdd
    -- Step 4: negate the limit. `∑ a i * b i = -∑ a i * (-b i)`.
    refine ⟨-y, ?_⟩
    have heq : (fun n => ∑ i ∈ range n, a i * b i)
        = (fun n => -(∑ i ∈ range n, a i * (-b i))) := by
      funext n
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [heq]
    exact hy.neg
