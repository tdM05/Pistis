import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology



/-Informal Statement

Prove that if $f$ is holomorphic in the unit disc, bounded and not identically zero, and $z_{1}, z_{2}, \ldots, z_{n}, \ldots$ are its zeros $\left(\left|z_{k}\right|<1\right)$, then $\sum_{n}\left(1-\left|z_{n}\right|\right)<\infty$.
-/

/-Informal Proof

Fix $\mathrm{N}$ and let $D(0, R)$ contains the first $\mathrm{N}$ zeroes of f. Let $S_N=\sum_{k=1}^N\left(1-\left|z_k\right|\right)=$ $\sum_{k=1}^N \int_{\left|z_k\right|}^1 1 d r$. Let $\eta_k$ be the characteristic function of the interval $\left.\| z_k \mid, 1\right]$. We have $S_N=\sum_{k=1}^N \int_0^1 \eta(r) d r=\int_0^1\left(\sum_{k=1}^N \eta_k(r)\right) d r \leq \int_0^1 n(r) d r$, where $n(r)$ is the number of zeroes of $f$ at the disk $D(0, r)$. For $r \leq 1$ we have $n(r) \leq \frac{n(r)}{r}$. This means that $S_N \leq \int_0^1 n(r) \frac{d r}{r}$. If $f(0)=0$ then we have $f(z)=z^m g(z)$ for some integer $\mathrm{m}$ and some holomorphic $g$ with $g(0) \neq 0$. The other zeroes of $\mathrm{f}$ are precisely the zeroes of $g$. Thus we have reduced the problem to $f(0) \neq 0$. By the Corollary of the Jensen's equality we get $S_N \leq \int_0^1 n(r) \frac{d r}{r}=\frac{1}{2 \pi} \int_0^{2 \pi} \log \left|f\left(R e^{i \pi}\right)\right| d \phi-\log |f(0)|<M$ since $f$ is bounded. The partial sums of the series are bounded and therefore the series converges.
-/

theorem Shakarchi_exercise_5_1 (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
  (hb : Bornology.IsBounded (Set.range f)) (h0 : f ≠ 0) (zeros : ℕ → ℂ)
  (hz : Set.range zeros = {z | f z = 0 ∧ z ∈ (ball (0 : ℂ) 1)}) :
  ∃ (l : ℝ), Tendsto (λ n => (∑ i ∈ range n, (1 - ‖zeros i‖))) atTop (𝓝 l) := by
  sorry

/-
## Why `Shakarchi_exercise_5_1` is false

The hypotheses only require `zeros : ℕ → ℂ` to hit every zero of `f` inside the unit disk at least
once. They do *not* prevent infinitely many repetitions of the very same zero. If we take a bounded
holomorphic function whose zero set inside the unit disk is `{0}` (for instance the function that
coincides with the identity map on the disk and is clamped to `0` outside), then the constant
sequence `zeros n = 0` still satisfies `Set.range zeros = {0}`. However, the series
`∑ (1 - ‖zeros n‖)` then becomes the harmonic series made of ones, so the partial sums are simply
`n` and have no finite limit. This shows that the original Lean statement is incorrect.
-/

namespace ProofNet367

noncomputable section

open scoped Classical Nat

def counterexampleF (z : ℂ) : ℂ :=
  if ‖z‖ < 1 then z else 0

def counterexampleZeros : ℕ → ℂ := fun _ => 0

lemma counterexampleF_eq_id {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    counterexampleF z = z := by
  have hz_norm : ‖z‖ < (1 : ℝ) := by
    have hz_dist : dist z (0 : ℂ) < 1 := by simpa [Metric.mem_ball] using hz
    simpa [Complex.dist_eq, sub_eq_add_neg, sub_zero] using hz_dist
  simp [counterexampleF, hz_norm]

lemma counterexample_differentiable :
    DifferentiableOn ℂ counterexampleF (ball (0 : ℂ) 1) := by
  classical
  have hid : DifferentiableOn ℂ (fun z : ℂ => z) (ball (0 : ℂ) 1) :=
    (differentiable_id).differentiableOn
  refine (DifferentiableOn.congr hid ?_)
  intro z hz
  exact counterexampleF_eq_id hz

lemma counterexample_bounded : Bornology.IsBounded (Set.range counterexampleF) := by
  classical
  have hbound :
      ∀ y ∈ Set.range counterexampleF, ‖y‖ ≤ (1 : ℝ) := by
    intro y hy
    rcases hy with ⟨z, rfl⟩
    by_cases hz : ‖z‖ < (1 : ℝ)
    · have hz_le : ‖z‖ ≤ (1 : ℝ) := le_of_lt hz
      simpa [counterexampleF, hz] using hz_le
    · have hz_ge : ¬ ‖z‖ < (1 : ℝ) := hz
      simp [counterexampleF, hz_ge]
  exact (isBounded_iff_forall_norm_le).2 ⟨1, hbound⟩

lemma counterexample_nonzero : counterexampleF ≠ (0 : ℂ → ℂ) := by
  classical
  let z : ℂ := (1 / 2 : ℝ)
  have hz_norm : ‖z‖ < (1 : ℝ) := by
    have hz_val : ‖z‖ = (1 / 2 : ℝ) := by simp [z]
    have hz_lt : (1 / 2 : ℝ) < 1 := by norm_num
    simpa [hz_val] using hz_lt
  have hz_eval : counterexampleF z = z := by
    have hz_ball : z ∈ ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, Complex.dist_eq, sub_eq_add_neg, sub_zero] using hz_norm
    exact counterexampleF_eq_id hz_ball
  intro h
  have hz_zero : counterexampleF z = 0 := congrArg (fun g : ℂ → ℂ => g z) h
  have hz_ne : z ≠ 0 := by
    simp [z]
  exact hz_ne (by simpa [hz_eval] using hz_zero)

lemma counterexample_zero_set :
    {z : ℂ | counterexampleF z = 0 ∧ z ∈ ball (0 : ℂ) 1} = ({0} : Set ℂ) := by
  classical
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hz_zero, hz_ball⟩
    have hz_id : counterexampleF z = z := counterexampleF_eq_id hz_ball
    have hz_eq : z = 0 := by simp [hz_id] at hz_zero; exact hz_zero
    simp [hz_eq]
  · intro hz
    rcases Set.mem_singleton_iff.1 hz with rfl
    have hnorm : ‖(0 : ℂ)‖ < (1 : ℝ) := by norm_num
    have hball : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by
      simp [Metric.mem_ball]
    simp [counterexampleF]

lemma counterexampleZeros_range :
    Set.range counterexampleZeros = ({0} : Set ℂ) := by
  classical
  ext z
  constructor
  · intro hz
    rcases hz with ⟨n, rfl⟩
    simp [counterexampleZeros]
  · intro hz
    rcases Set.mem_singleton_iff.1 hz with rfl
    exact ⟨0, by simp [counterexampleZeros]⟩

lemma counterexample_partialSums (n : ℕ) :
    (∑ i ∈ range n, (1 - ‖counterexampleZeros i‖)) = (n : ℝ) := by
  classical
  simp [counterexampleZeros]

lemma not_tendsto_nat_cast_atTop_nhds (l : ℝ) :
    ¬ Tendsto (fun n : ℕ => (n : ℝ)) atTop (𝓝 l) := by
  classical
  intro h
  have hball := h (Metric.ball_mem_nhds l (zero_lt_one : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1 hball)
  set m := max N ⌈l + 2⌉₊ with hm_def
  have hm_ge : N ≤ m := le_max_left _ _
  have hm_small : dist (m : ℝ) l < 1 := hN m hm_ge
  have hm_large : (l + 2 : ℝ) ≤ (m : ℝ) := by
    have : (⌈l + 2⌉₊ : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (le_max_right N ⌈l + 2⌉₊)
    exact (Nat.le_ceil (l + 2 : ℝ)).trans this
  have hlm : l ≤ (m : ℝ) := by linarith [hm_large]
  have hdist_eq :
      dist (m : ℝ) l = (m : ℝ) - l := by
    have hnonneg : 0 ≤ (m : ℝ) - l := sub_nonneg.mpr hlm
    simpa [Real.dist_eq, abs_of_nonneg hnonneg, sub_eq_add_neg]
  have hdist_ge2 : (2 : ℝ) ≤ dist (m : ℝ) l := by
    have hsub : (2 : ℝ) ≤ (m : ℝ) - l := by linarith [hm_large]
    simpa [hdist_eq]
  have hdist_ge1 : (1 : ℝ) ≤ dist (m : ℝ) l :=
    (show (1 : ℝ) ≤ (2 : ℝ) by norm_num).trans hdist_ge2
  exact (not_lt_of_ge hdist_ge1) hm_small

theorem Shakarchi_exercise_5_1_neg :
    ∃ (f : ℂ → ℂ) (_hf : DifferentiableOn ℂ f (ball 0 1))
      (_hb : Bornology.IsBounded (Set.range f)) (_h0 : f ≠ 0) (zeros : ℕ → ℂ)
      (_hz : Set.range zeros = {z | f z = 0 ∧ z ∈ (ball (0 : ℂ) 1)}),
        ¬ ∃ l : ℝ, Tendsto (fun n => ∑ i ∈ range n, (1 - ‖zeros i‖)) atTop (𝓝 l) := by
  classical
  refine ⟨counterexampleF, counterexample_differentiable, counterexample_bounded,
    counterexample_nonzero, counterexampleZeros, ?_, ?_⟩
  · exact (counterexampleZeros_range.trans counterexample_zero_set.symm)
  · have hsum :
        (fun n => ∑ i ∈ range n, (1 - ‖counterexampleZeros i‖)) =
          fun n : ℕ => (n : ℝ) := by
      funext n
      exact counterexample_partialSums n
    have hcontr :
        ¬ ∃ l, Tendsto (fun n : ℕ => (n : ℝ)) atTop (𝓝 l) := by
      intro h
      obtain ⟨l, hl⟩ := h
      exact (not_tendsto_nat_cast_atTop_nhds l) hl
    intro h
    apply hcontr
    rcases h with ⟨l, hl⟩
    have hlimit :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop (𝓝 l) :=
      (hsum ▸ hl : _)
    exact ⟨l, hlimit⟩

/-
## Why the Original Formalization is Not Faithful

The original formalization `Shakarchi_exercise_5_1` uses a sequence
`zeros : ℕ → ℂ` together with only the range condition
`Set.range zeros = {z | f z = 0 ∧ z ∈ ball 0 1}`.  That range condition says that the
sequence hits exactly the geometric zero set, but it does not say that the sequence lists zeros
without repetition or with the correct multiplicity.  In particular, the same zero can be repeated
infinitely many times.  The negation theorem `Shakarchi_exercise_5_1_neg` above demonstrates this.

There is a second mismatch: the hypothesis `f ≠ 0` is a global statement about the auxiliary
function `f : ℂ → ℂ`, while the theorem is about the restriction of `f` to the unit disc.  The
faithful non-vanishing hypothesis is that `f` is not identically zero on `ball 0 1`.

## Correction

The corrected statement below makes four changes.

1. It replaces `f ≠ 0` with `¬ Set.EqOn f 0 (ball 0 1)`, i.e. `f` is not identically zero on
   the unit disc.
2. It replaces `Bornology.IsBounded (Set.range f)` with
   `Bornology.IsBounded (f '' ball 0 1)`, matching boundedness on the unit disc.
3. It removes the external sequence `zeros : ℕ → ℂ` and indexes the series directly by the
   subtype of zeros in the unit disc.  This handles both finite and infinite zero sets without
   requiring an artificial enumeration.
4. It weights each geometric zero by `(analyticOrderAt f z).toNat`, so the statement counts zeros
   with their analytic multiplicities, as in the classical Blaschke condition.
-/

private lemma Shakarchi_exercise_5_1_choose_radius
    (f : ℂ → ℂ)
    (s : Finset {z : ℂ // f z = 0 ∧ z ∈ ball (0 : ℂ) 1}) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧ (∀ z ∈ s, ‖(z : ℂ)‖ < R) ∧
      ((((∑ z ∈ s, (analyticOrderAt f (z : ℂ)).toNat : ℝ) +
        ((analyticOrderAt f (0 : ℂ)).toNat : ℝ)) * (-Real.log R)) ≤ 1) := by
  classical
  -- Step 1: First choose any radius `Rlow < 1` enclosing the finite set of selected zeros.
  -- Step 1.1: This is a purely finite compactness-free argument: enlarge the radius one zero at a
  -- time, and after each insertion average the current maximum with `1`.
  obtain ⟨Rlow, hRlow_pos, hRlow_lt_one, hRlow_all⟩ :
      ∃ Rlow : ℝ, 0 < Rlow ∧ Rlow < 1 ∧ ∀ z ∈ s, ‖(z : ℂ)‖ < Rlow := by
    induction s using Finset.induction with
    | empty =>
        -- Step 1.2: The empty finite set is enclosed by radius `1 / 2`.
        exact ⟨(1 / 2 : ℝ), by norm_num, by norm_num, by simp⟩
    | insert a s ha ih =>
        -- Step 1.3: For an insertion, start from the induction radius and the new zero norm.
        rcases ih with ⟨r, hrpos, hrlt, hrall⟩
        let q : ℝ := max r ‖(a : ℂ)‖
        refine ⟨(q + 1) / 2, ?_, ?_, ?_⟩
        · -- Step 1.4: The midpoint with `1` is positive.
          have hq_nonneg : 0 ≤ q := by
            exact le_trans (norm_nonneg (a : ℂ)) (le_max_right r ‖(a : ℂ)‖)
          linarith
        · -- Step 1.5: The midpoint is still strictly less than `1`.
          have hnorm_a_lt : ‖(a : ℂ)‖ < 1 := by
            simpa [Metric.mem_ball, dist_zero_right] using a.2.2
          have hq_lt : q < 1 := max_lt hrlt hnorm_a_lt
          linarith
        · -- Step 1.6: Every old zero and the newly inserted zero lie below the new radius.
          intro z hz
          have hq_lt_mid : q < (q + 1) / 2 := by
            have hnorm_a_lt : ‖(a : ℂ)‖ < 1 := by
              simpa [Metric.mem_ball, dist_zero_right] using a.2.2
            have hq_lt_one : q < 1 := max_lt hrlt hnorm_a_lt
            linarith
          rw [Finset.mem_insert] at hz
          rcases hz with hza | hz
          · subst z
            exact (le_max_right r ‖(a : ℂ)‖).trans_lt hq_lt_mid
          · exact ((hrall z hz).trans_le (le_max_left r ‖(a : ℂ)‖)).trans hq_lt_mid
  -- Step 2: Push the enclosing radius closer to `1` so the future `-log R` error is tiny.
  -- Step 2.1: `nTot` is the selected multiplicity plus the possible zero multiplicity at the
  -- origin, which is the correction term appearing in Jensen's formula.
  let nTot : ℕ :=
    (∑ z ∈ s, (analyticOrderAt f (z : ℂ)).toNat) + (analyticOrderAt f (0 : ℂ)).toNat
  -- Step 2.2: Choose `E = exp(-1/(nTot+1))`; then `nTot * (-log E) < 1`.
  let E : ℝ := Real.exp (-(1 : ℝ) / ((nTot : ℝ) + 1))
  -- Step 2.3: The final radius is the larger of the enclosing radius and this logarithmic cutoff.
  let R : ℝ := max Rlow E
  have hEpos : 0 < E := by
    dsimp [E]
    positivity
  have hElt_one : E < 1 := by
    dsimp [E]
    rw [Real.exp_lt_one_iff]
    have hden_pos : 0 < (nTot : ℝ) + 1 := by positivity
    have hfrac_pos : 0 < (1 : ℝ) / ((nTot : ℝ) + 1) := by positivity
    have hrewrite :
        (-(1 : ℝ) / ((nTot : ℝ) + 1)) = -((1 : ℝ) / ((nTot : ℝ) + 1)) := by
      ring
    rw [hrewrite]
    exact neg_neg_of_pos hfrac_pos
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · -- Step 2.4: The final radius is positive.
    exact lt_of_lt_of_le hEpos (le_max_right Rlow E)
  · -- Step 2.5: The final radius is still strictly inside the unit disc.
    exact max_lt hRlow_lt_one hElt_one
  · -- Step 2.6: The final radius still contains all selected zeros.
    intro z hz
    exact (hRlow_all z hz).trans_le (le_max_left Rlow E)
  · -- Step 2.7: The definition of `E` gives the desired bound on `-log R`.
    have hlogE_le_logR : Real.log E ≤ Real.log R := by
      apply Real.log_le_log hEpos
      exact le_max_right Rlow E
    have hlogE : Real.log E = -(1 : ℝ) / ((nTot : ℝ) + 1) := by
      dsimp [E]
      rw [Real.log_exp]
    have hneglogR_le : -Real.log R ≤ (1 : ℝ) / ((nTot : ℝ) + 1) := by
      rw [hlogE] at hlogE_le_logR
      have hrewrite :
          (-(1 : ℝ) / ((nTot : ℝ) + 1)) = -((1 : ℝ) / ((nTot : ℝ) + 1)) := by
        ring
      rw [hrewrite] at hlogE_le_logR
      linarith
    have hsum_eq :
        ((∑ z ∈ s, (analyticOrderAt f (z : ℂ)).toNat : ℝ) +
          ((analyticOrderAt f (0 : ℂ)).toNat : ℝ)) = (nTot : ℝ) := by
      simp [nTot]
    rw [hsum_eq]
    have hden_pos : 0 < (nTot : ℝ) + 1 := by positivity
    have hn_le : (nTot : ℝ) / ((nTot : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hden_pos]
      linarith
    calc (nTot : ℝ) * (-Real.log R)
        ≤ (nTot : ℝ) * ((1 : ℝ) / ((nTot : ℝ) + 1)) := by
          exact mul_le_mul_of_nonneg_left hneglogR_le (by positivity)
      _ = (nTot : ℝ) / ((nTot : ℝ) + 1) := by ring
      _ ≤ 1 := hn_le

private lemma Shakarchi_exercise_5_1_finite_sum_le_jensen
    (f : ℂ → ℂ) (hf_analytic : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1))
    (hneqtop : ∀ z ∈ ball (0 : ℂ) 1, analyticOrderAt f z ≠ ⊤)
    (s : Finset {z : ℂ // f z = 0 ∧ z ∈ ball (0 : ℂ) 1})
    {R : ℝ} (hRpos : 0 < R) (hRlt : R < 1)
    (hRall : ∀ z ∈ s, ‖(z : ℂ)‖ < R)
    (hRerr :
      (((∑ z ∈ s, (analyticOrderAt f (z : ℂ)).toNat : ℝ) +
        ((analyticOrderAt f (0 : ℂ)).toNat : ℝ)) * (-Real.log R) ≤ 1)) :
    (∑ z ∈ s, ((analyticOrderAt f (z : ℂ)).toNat : ℝ) * (1 - ‖(z : ℂ)‖))
      ≤ ((analyticOrderAt f (0 : ℂ)).toNat : ℝ) +
        ((∑ᶠ (u : ℂ), ((MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|)) u : ℝ) *
            Real.log (R * ‖(0 : ℂ) - u‖⁻¹) +
          ((MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|)) (0 : ℂ) : ℝ) * Real.log R)) +
        1 := by
  classical
  -- Step 1: Introduce compact notation for the zero subtype, divisor, multiplicity, and Jensen
  -- logarithmic summand.  These abbreviations make the comparison algebra readable.
  let Z := {z : ℂ // f z = 0 ∧ z ∈ ball (0 : ℂ) 1}
  let D := MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|)
  let mult : Z → ℝ := fun z => ((analyticOrderAt f (z : ℂ)).toNat : ℝ)
  let summand : Z → ℝ := fun z => mult z * (1 - ‖(z : ℂ)‖)
  let logTerm : ℂ → ℝ := fun u => (D u : ℝ) * Real.log (R * ‖(0 : ℂ) - u‖⁻¹)
  -- Step 1.1: Split the finite selected zero set into the origin and non-origin parts.
  let sz : Finset Z := Finset.filter (fun z : Z => (z : ℂ) = 0) s
  let snz : Finset Z := Finset.filter (fun z : Z => ¬ (z : ℂ) = 0) s
  -- Step 2: Restrict analyticity and the divisor to the closed ball of radius `R`.
  have hRabs : |R| = R := abs_of_pos hRpos
  have hclosed_sub : closedBall (0 : ℂ) |R| ⊆ ball (0 : ℂ) 1 := by
    simpa [hRabs] using (Metric.closedBall_subset_ball (x := (0 : ℂ)) hRlt)
  have hfR_an : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |R|) := hf_analytic.mono hclosed_sub
  have hfR_mer : MeromorphicOn f (closedBall (0 : ℂ) |R|) := hfR_an.meromorphicOn
  have hD_nonneg : 0 ≤ D := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfR_an
  have hlogR_nonpos : Real.log R ≤ 0 := Real.log_nonpos hRpos.le (le_of_lt hRlt)
  have hneglogR_nonneg : 0 ≤ -Real.log R := by linarith
  -- Step 2.1: On an actual zero in the closed ball, the meromorphic divisor equals the analytic
  -- multiplicity.  This is the bridge between Jensen's divisor and the theorem's summand.
  have hD_eq_mult (z : Z) (hzR : (z : ℂ) ∈ closedBall (0 : ℂ) |R|) :
      (D (z : ℂ) : ℝ) = mult z := by
    have hz_an : AnalyticAt ℂ f (z : ℂ) := hf_analytic (z : ℂ) z.2.2
    have hZ : ((D (z : ℂ) : ℤ) = ((analyticOrderAt f (z : ℂ)).toNat : ℤ)) := by
      simp only [D]
      rw [MeromorphicOn.divisor_apply hfR_mer hzR]
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hneqtop (z : ℂ) z.2.2)
      rw [hz_an.meromorphicOrderAt_eq]
      rw [← hn]
      simp
    show (↑(D ↑z) : ℝ) = ((analyticOrderAt f (z : ℂ)).toNat : ℝ)
    exact_mod_cast hZ
  -- Step 2.2: The same divisor/multiplicity conversion at the origin supplies Jensen's central
  -- correction term.
  have hD0_eq_mult0 :
      (D (0 : ℂ) : ℝ) = ((analyticOrderAt f (0 : ℂ)).toNat : ℝ) := by
    have hz0_ball : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp [Metric.mem_ball]
    have hz0_closed : (0 : ℂ) ∈ closedBall (0 : ℂ) |R| := by
      simp [Metric.mem_closedBall, hRabs, le_of_lt hRpos]
    have hz_an : AnalyticAt ℂ f (0 : ℂ) := hf_analytic (0 : ℂ) hz0_ball
    have hZ : ((D (0 : ℂ) : ℤ) = ((analyticOrderAt f (0 : ℂ)).toNat : ℤ)) := by
      simp only [D]
      rw [MeromorphicOn.divisor_apply hfR_mer hz0_closed]
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hneqtop (0 : ℂ) hz0_ball)
      rw [hz_an.meromorphicOrderAt_eq]
      rw [← hn]
      simp
    show (↑(D (0 : ℂ)) : ℝ) = ((analyticOrderAt f (0 : ℂ)).toNat : ℝ)
    exact_mod_cast hZ
  -- Step 3: Jensen's logarithmic terms are nonnegative on the selected closed ball.
  have hlogTerm_nonneg : ∀ u : ℂ, 0 ≤ logTerm u := by
    intro u
    by_cases hu : u ∈ closedBall (0 : ℂ) |R|
    · by_cases hu0 : u = 0
      · simp [logTerm, hu0]
      · have hDu_nonneg : 0 ≤ (D u : ℝ) := by exact_mod_cast hD_nonneg u
        have hnorm_pos : 0 < ‖(0 : ℂ) - u‖ := by
          have h0u : (0 : ℂ) ≠ u := by
            intro h0u
            exact hu0 h0u.symm
          exact norm_pos_iff.mpr (sub_ne_zero.mpr h0u)
        have hle : ‖(0 : ℂ) - u‖ ≤ R := by
          simpa [Metric.mem_closedBall, hRabs] using hu
        have hone_le : 1 ≤ R / ‖(0 : ℂ) - u‖ := (one_le_div hnorm_pos).2 hle
        have hlog_nonneg : 0 ≤ Real.log (R * ‖(0 : ℂ) - u‖⁻¹) := by
          have hrewrite : R * ‖(0 : ℂ) - u‖⁻¹ = R / ‖(0 : ℂ) - u‖ := by
            rw [div_eq_mul_inv]
          rw [hrewrite]
          exact Real.log_nonneg hone_le
        exact mul_nonneg hDu_nonneg hlog_nonneg
    · have hDzero : D u = 0 := by
        exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem D hu
      simp [logTerm, hDzero]
  -- Step 3.1: The support of the logarithmic Jensen summand is finite, because the divisor has
  -- finite support on the compact closed ball.
  have hlogTerm_support_finite : (Function.support logTerm).Finite := by
    have hDsupport : (Function.support D).Finite := D.finiteSupport (isCompact_closedBall (0 : ℂ) |R|)
    exact hDsupport.subset (by
      intro u hu
      simp only [Function.mem_support, logTerm, ne_eq, mul_eq_zero, Int.cast_eq_zero,
        not_or] at hu
      exact hu.1)
  -- Step 4: Bound the possible contribution of the origin by its multiplicity at `0`.
  have hzero_sum_le :
      (∑ z ∈ sz, summand z) ≤ ((analyticOrderAt f (0 : ℂ)).toNat : ℝ) := by
    have hcard : sz.card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro x y hx hy
      have hx0 : (x : ℂ) = 0 := by
        change x ∈ Finset.filter (fun z : Z => (z : ℂ) = 0) s at hx
        exact (Finset.mem_filter.mp hx).2
      have hy0 : (y : ℂ) = 0 := by
        change y ∈ Finset.filter (fun z : Z => (z : ℂ) = 0) s at hy
        exact (Finset.mem_filter.mp hy).2
      exact Subtype.ext (hx0.trans hy0.symm)
    have hterm : ∀ z ∈ sz, summand z = ((analyticOrderAt f (0 : ℂ)).toNat : ℝ) := by
      intro z hz
      simp [sz] at hz
      have hz0 : (z : ℂ) = 0 := hz.2
      simp [summand, mult, hz0]
    calc
      (∑ z ∈ sz, summand z)
          = (∑ z ∈ sz, ((analyticOrderAt f (0 : ℂ)).toNat : ℝ)) := by
              exact Finset.sum_congr rfl hterm
      _ = (sz.card : ℝ) * ((analyticOrderAt f (0 : ℂ)).toNat : ℝ) := by simp
      _ ≤ (1 : ℝ) * ((analyticOrderAt f (0 : ℂ)).toNat : ℝ) := by
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = ((analyticOrderAt f (0 : ℂ)).toNat : ℝ) := by ring
  -- Step 5: Compare every nonzero selected zero with the corresponding Jensen logarithmic term.
  have hnonzero_each :
      ∀ z ∈ snz, summand z ≤ logTerm (z : ℂ) + mult z * (-Real.log R) := by
    intro z hz
    simp [snz] at hz
    have hz_mem_s : z ∈ s := hz.1
    have hz_ne : (z : ℂ) ≠ 0 := hz.2
    have hz_norm_pos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr hz_ne
    have hz_norm_lt_R : ‖(z : ℂ)‖ < R := hRall z hz_mem_s
    have hz_closed : (z : ℂ) ∈ closedBall (0 : ℂ) |R| := by
      simp [Metric.mem_closedBall, dist_zero_right, hRabs, le_of_lt hz_norm_lt_R]
    have hD_eq : (D (z : ℂ) : ℝ) = mult z := hD_eq_mult z hz_closed
    -- Step 5.1: The elementary inequality `1 - r ≤ log(1/r)` handles the Blaschke summand.
    have hlog_inv_bound : 1 - ‖(z : ℂ)‖ ≤ Real.log (‖(z : ℂ)‖⁻¹) := by
      simpa [inv_inv] using Real.one_sub_inv_le_log_of_pos (inv_pos.mpr hz_norm_pos)
    -- Step 5.2: Rewrite `log(1/‖z‖)` as the Jensen logarithm minus `log R`.
    have hlog_eq :
        Real.log (‖(z : ℂ)‖⁻¹) =
          Real.log (R * ‖(z : ℂ)‖⁻¹) - Real.log R := by
      rw [Real.log_mul (ne_of_gt hRpos) (inv_ne_zero (norm_ne_zero_iff.mpr hz_ne)), Real.log_inv]
      ring
    have hbase : 1 - ‖(z : ℂ)‖ ≤ Real.log (R * ‖(z : ℂ)‖⁻¹) - Real.log R := by
      rwa [hlog_eq] at hlog_inv_bound
    have hm_nonneg : 0 ≤ mult z := by positivity
    have hmul : mult z * (1 - ‖(z : ℂ)‖) ≤
        mult z * (Real.log (R * ‖(z : ℂ)‖⁻¹) - Real.log R) := by
      exact mul_le_mul_of_nonneg_left hbase hm_nonneg
    have hnorm_sub : ‖(0 : ℂ) - (z : ℂ)‖ = ‖(z : ℂ)‖ := by simp
    simp only [summand, logTerm]
    rw [hD_eq, hnorm_sub]
    linarith
  -- Step 5.3: Sum the pointwise comparison over all nonzero selected zeros.
  have hnonzero_sum_le :
      (∑ z ∈ snz, summand z) ≤
        (∑ z ∈ snz, logTerm (z : ℂ)) + (∑ z ∈ snz, mult z) * (-Real.log R) := by
    calc
      (∑ z ∈ snz, summand z)
          ≤ ∑ z ∈ snz, (logTerm (z : ℂ) + mult z * (-Real.log R)) := by
              exact Finset.sum_le_sum hnonzero_each
      _ = (∑ z ∈ snz, logTerm (z : ℂ)) + ∑ z ∈ snz, mult z * (-Real.log R) := by
              simp [Finset.sum_add_distrib]
      _ = (∑ z ∈ snz, logTerm (z : ℂ)) + (∑ z ∈ snz, mult z) * (-Real.log R) := by
              rw [Finset.sum_mul]
  -- Step 6: Bound the selected Jensen terms by the full finite-support Jensen finsum.
  have hselected_log_le_finsum :
      (∑ z ∈ snz, logTerm (z : ℂ)) ≤ ∑ᶠ u : ℂ, logTerm u := by
    have hinj : Set.InjOn (fun z : Z => (z : ℂ)) (snz : Set Z) := by
      intro x hx y hy hxy
      exact Subtype.ext hxy
    have hsum_image :
        (∑ u ∈ Finset.image (fun z : Z => (z : ℂ)) snz, logTerm u) =
          ∑ z ∈ snz, logTerm (z : ℂ) := by
      exact Finset.sum_image hinj
    have hsupp_sum : ∑ᶠ u : ℂ, logTerm u =
        ∑ u ∈ hlogTerm_support_finite.toFinset, logTerm u := by
      exact finsum_eq_sum logTerm hlogTerm_support_finite
    rw [← hsum_image, hsupp_sum]
    let im := Finset.image (fun z : Z => (z : ℂ)) snz
    let S := hlogTerm_support_finite.toFinset
    have hsum_im_eq_filter :
        (∑ u ∈ im, logTerm u) = ∑ u ∈ Finset.filter (fun u : ℂ => u ∈ im) S, logTerm u := by
      symm
      exact Finset.sum_subset (by
        intro u hu
        exact (Finset.mem_filter.mp hu).2) (by
        intro u huIm huNot
        have huNotS : u ∉ S := by
          intro huS
          exact huNot (Finset.mem_filter.mpr ⟨huS, huIm⟩)
        have hnot_support : u ∉ Function.support logTerm := by
          intro hsupp
          exact huNotS ((Set.Finite.mem_toFinset hlogTerm_support_finite).mpr hsupp)
        have htu : logTerm u = 0 := by
          simpa [Function.mem_support] using hnot_support
        exact htu)
    rw [hsum_im_eq_filter]
    exact Finset.sum_le_sum_of_subset_of_nonneg (by
      intro u hu
      simp at hu
      exact hu.1) (by
      intro u huS huFilter
      exact hlogTerm_nonneg u)
  -- Step 7: The nonzero selected multiplicity is bounded by the full selected multiplicity.
  have hsnz_mult_le :
      (∑ z ∈ snz, mult z) + ((analyticOrderAt f (0 : ℂ)).toNat : ℝ) ≤
        (∑ z ∈ s, mult z) + ((analyticOrderAt f (0 : ℂ)).toNat : ℝ) := by
    have hsum_le : (∑ z ∈ snz, mult z) ≤ ∑ z ∈ s, mult z := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (by
        intro z hz
        exact (Finset.mem_filter.mp hz).1) (by
        intro z hzS hzNot
        show 0 ≤ mult z
        positivity)
    exact add_le_add hsum_le le_rfl
  -- Step 7.1: Therefore the chosen radius makes the total logarithmic error at most `1`.
  have herror_le :
      (((∑ z ∈ snz, mult z) + ((analyticOrderAt f (0 : ℂ)).toNat : ℝ)) * (-Real.log R)) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right hsnz_mult_le hneglogR_nonneg).trans hRerr
  -- Step 8: Reassemble the zero/nonzero split and insert Jensen's central correction.
  have hsplit :
      (∑ z ∈ sz, summand z) + (∑ z ∈ snz, summand z) =
        ∑ z ∈ s, summand z := by
    simpa [sz, snz] using
      (Finset.sum_filter_add_sum_filter_not s (fun z : Z => (z : ℂ) = 0) summand)
  have hmain :
      (∑ z ∈ s, summand z) ≤
        ((analyticOrderAt f (0 : ℂ)).toNat : ℝ) +
          ((∑ᶠ u : ℂ, logTerm u) + (D (0 : ℂ) : ℝ) * Real.log R) + 1 := by
    rw [← hsplit]
    calc
      (∑ z ∈ sz, summand z) + (∑ z ∈ snz, summand z)
          ≤ ((analyticOrderAt f (0 : ℂ)).toNat : ℝ) +
              ((∑ z ∈ snz, logTerm (z : ℂ)) +
                (∑ z ∈ snz, mult z) * (-Real.log R)) := by
              linarith [hzero_sum_le, hnonzero_sum_le]
      _ ≤ ((analyticOrderAt f (0 : ℂ)).toNat : ℝ) +
              ((∑ᶠ u : ℂ, logTerm u) +
                (∑ z ∈ snz, mult z) * (-Real.log R)) := by
              gcongr
      _ = ((analyticOrderAt f (0 : ℂ)).toNat : ℝ) +
              (((∑ᶠ u : ℂ, logTerm u) + (D (0 : ℂ) : ℝ) * Real.log R) +
                (((∑ z ∈ snz, mult z) + ((analyticOrderAt f (0 : ℂ)).toNat : ℝ)) *
                  (-Real.log R))) := by
              rw [hD0_eq_mult0]
              ring
      _ ≤ ((analyticOrderAt f (0 : ℂ)).toNat : ℝ) +
              ((∑ᶠ u : ℂ, logTerm u) + (D (0 : ℂ) : ℝ) * Real.log R) + 1 := by
              linarith
  simpa [summand, mult, logTerm, D] using hmain

private lemma Shakarchi_exercise_5_1_jensen_bound
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hb : Bornology.IsBounded (f '' (ball (0 : ℂ) 1)))
    {R : ℝ} (hRpos : 0 < R) (hRlt : R < 1) :
    (∑ᶠ (u : ℂ), ((MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|)) u : ℝ) *
        Real.log (R * ‖(0 : ℂ) - u‖⁻¹) +
      ((MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|)) (0 : ℂ) : ℝ) * Real.log R)
      ≤ Real.log (max (Classical.choose (isBounded_iff_forall_norm_le.mp hb)) 1) -
        Real.log ‖meromorphicTrailingCoeffAt f (0 : ℂ)‖ := by
  classical
  -- Step 1: Extract a uniform bound for `‖f z‖` on the unit disc and replace it by `A ≥ 1`.
  let M : ℝ := Classical.choose (isBounded_iff_forall_norm_le.mp hb)
  have hM : ∀ x ∈ f '' ball (0 : ℂ) 1, ‖x‖ ≤ M :=
    Classical.choose_spec (isBounded_iff_forall_norm_le.mp hb)
  let A : ℝ := max M 1
  have hA1 : 1 ≤ A := by simp [A]
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  -- Step 2: Restrict holomorphicity from the unit disc to the closed ball of radius `R`.
  have hf_analytic : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1) := hf.analyticOnNhd isOpen_ball
  have hRabs : |R| = R := abs_of_pos hRpos
  have hsub : closedBall (0 : ℂ) |R| ⊆ ball (0 : ℂ) 1 := by
    simpa [hRabs] using (Metric.closedBall_subset_ball (x := (0 : ℂ)) hRlt)
  have hfR_an : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |R|) := hf_analytic.mono hsub
  have hfR_mer : MeromorphicOn f (closedBall (0 : ℂ) |R|) := hfR_an.meromorphicOn
  -- Step 3: Bound the circle average of `log ‖f‖` by `log A`.
  have hcircle_le : Real.circleAverage (fun x => Real.log ‖f x‖) (0 : ℂ) R ≤ Real.log A := by
    apply Real.circleAverage_mono_on_of_le_circle
    · exact circleIntegrable_log_norm_meromorphicOn
        ((hfR_an.mono Metric.sphere_subset_closedBall).meromorphicOn)
    · intro x hx
      have hxball : x ∈ ball (0 : ℂ) 1 := hsub (Metric.sphere_subset_closedBall hx)
      have hxnorm_le_M : ‖f x‖ ≤ M := hM (f x) ⟨x, hxball, rfl⟩
      have hxnorm_le_A : ‖f x‖ ≤ A := hxnorm_le_M.trans (le_max_left M 1)
      by_cases hxzero : f x = 0
      · have hlogA_nonneg : 0 ≤ Real.log A := Real.log_nonneg hA1
        simpa [hxzero] using hlogA_nonneg
      · exact Real.log_le_log (norm_pos_iff.mpr hxzero) hxnorm_le_A
  -- Step 4: Jensen's formula rewrites that circle-average bound as a bound on the divisor sum.
  have hJ := MeromorphicOn.circleAverage_log_norm (c := (0 : ℂ)) (R := R) (f := f)
    (ne_of_gt hRpos) hfR_mer
  linarith

theorem Shakarchi_exercise_5_1_corrected
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hb : Bornology.IsBounded (f '' (ball (0 : ℂ) 1)))
    (h0 : ¬ Set.EqOn f (0 : ℂ → ℂ) (ball (0 : ℂ) 1)) :
    Summable (fun z : {z : ℂ // f z = 0 ∧ z ∈ ball (0 : ℂ) 1} =>
      ((analyticOrderAt f (z : ℂ)).toNat : ℝ) * (1 - ‖(z : ℂ)‖)) := by
  classical
  -- Step 1: Convert holomorphicity on the open unit disc into `AnalyticOnNhd`.
  -- Step 1.1: This is the analytic hypothesis needed both for the identity principle and for
  -- Jensen's divisor machinery.
  have hf_analytic : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1) := hf.analyticOnNhd isOpen_ball
  -- Step 2: Use the corrected non-identically-zero hypothesis to find one nonzero value in the
  -- unit disc.
  -- Step 2.1: If no such point existed, then `f` would be identically zero on the disc, contrary to
  -- `h0`.
  obtain ⟨zstar, hzstar_ball, hzstar_ne⟩ : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0 := by
    by_contra h
    apply h0
    intro z hz
    by_contra hz_ne_zero
    exact h ⟨z, hz, hz_ne_zero⟩
  -- Step 3: Prove that no zero in the unit disc has infinite analytic order.
  -- Step 3.1: The unit disc is preconnected, so a zero of infinite order would force local
  -- equality with `0`, hence global equality with `0` on the disc by the identity theorem.
  have hpre : IsPreconnected (ball (0 : ℂ) 1) := (convex_ball (0 : ℂ) 1).isPreconnected
  have hneqtop : ∀ z ∈ ball (0 : ℂ) 1, analyticOrderAt f z ≠ ⊤ := by
    intro z hz htop
    -- Step 3.2: Infinite analytic order means that `f` vanishes in a neighborhood of `z`.
    have hvanish_near : ∀ᶠ y in 𝓝 z, f y = 0 := analyticOrderAt_eq_top.mp htop
    -- Step 3.3: Use the identity theorem to propagate that local equality across the unit disc.
    have hEqOn_zero : Set.EqOn f (0 : ℂ → ℂ) (ball (0 : ℂ) 1) := by
      have hlocal : f =ᶠ[𝓝 z] (0 : ℂ → ℂ) := by
        filter_upwards [hvanish_near] with y hy
        simpa using hy
      have hzero_analytic : AnalyticOnNhd ℂ (0 : ℂ → ℂ) (ball (0 : ℂ) 1) :=
        analyticOnNhd_const
      exact hf_analytic.eqOn_of_preconnected_of_eventuallyEq hzero_analytic hpre hz hlocal
    -- Step 3.4: This contradicts the nonzero witness from Step 2.
    exact hzstar_ne (hEqOn_zero hzstar_ball)
  -- Step 4: Establish nonnegativity of the summands, needed for Mathlib's real summability
  -- criterion by bounded finite sums.
  have h_nonneg :
      0 ≤ fun z : {z : ℂ // f z = 0 ∧ z ∈ ball (0 : ℂ) 1} =>
        ((analyticOrderAt f (z : ℂ)).toNat : ℝ) * (1 - ‖(z : ℂ)‖) := by
    intro z
    -- Step 4.1: Every indexed zero lies strictly inside the unit disc.
    have hnorm_lt : ‖(z : ℂ)‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using z.2.2
    -- Step 4.2: Therefore the geometric factor `1 - ‖z‖` is nonnegative.
    have hgeom_nonneg : 0 ≤ 1 - ‖(z : ℂ)‖ := by linarith
    -- Step 4.3: Multiplicity is a natural number, hence nonnegative after casting to `ℝ`.
    exact mul_nonneg (by positivity) hgeom_nonneg
  -- Step 5: It suffices to bound every finite partial sub-sum by one global constant.
  -- Step 5.1: The constant below is the usual Jensen bound, with `+1` for the radius-choice error
  -- and another finite term for a possible zero at the origin.
  let M : ℝ := Classical.choose (isBounded_iff_forall_norm_le.mp hb)
  let C : ℝ :=
    ((analyticOrderAt f (0 : ℂ)).toNat : ℝ) +
      (Real.log (max M 1) - Real.log ‖meromorphicTrailingCoeffAt f (0 : ℂ)‖) + 1
  refine summable_of_sum_le (c := C) h_nonneg ?_
  intro s
  -- Step 6: Choose a radius `R < 1` that contains the finite set `s` and makes the logarithmic
  -- error term at most `1`.
  rcases Shakarchi_exercise_5_1_choose_radius f s with
    ⟨R, hRpos, hRlt, hRall, hRerr⟩
  -- Step 7: Compare the finite Blaschke sum over `s` with Jensen's finite-support divisor sum.
  have hfinite_le :=
    Shakarchi_exercise_5_1_finite_sum_le_jensen f hf_analytic hneqtop s hRpos hRlt hRall hRerr
  -- Step 8: Bound the Jensen divisor sum using boundedness of `f` on the unit disc.
  have hJensen_le :=
    Shakarchi_exercise_5_1_jensen_bound f hf hb hRpos hRlt
  -- Step 9: Combine the two inequalities and unfold the chosen constant.
  change
    (∑ z ∈ s, ((analyticOrderAt f (z : ℂ)).toNat : ℝ) * (1 - ‖(z : ℂ)‖)) ≤ C
  dsimp [C, M]
  linarith

end

end ProofNet367
