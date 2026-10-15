import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- We always consider limsups of sequences along the filter `atTop`.
local notation "limsup" => fun u : ℕ → EReal => Filter.limsup u Filter.atTop



/-Informal Statement

For any two real sequences $\left\{a_{n}\right\},\left\{b_{n}\right\}$, prove that $\limsup _{n \rightarrow \infty}\left(a_{n}+b_{n}\right) \leq \limsup _{n \rightarrow \infty} a_{n}+\limsup _{n \rightarrow \infty} b_{n},$ provided the sum on the right is not of the form $\infty-\infty$.
-/

/-Informal Proof

Since the case when $\limsup _{n \rightarrow \infty} a_n=+\infty$ and $\limsup _{n \rightarrow \infty} b_n=-\infty$ has been excluded from consideration, we note that the inequality is obvious if $\limsup _{n \rightarrow \infty} a_n=+\infty$. Hence we shall assume that $\left\{a_n\right\}$ is bounded above.

Let $\left\{n_k\right\}$ be a subsequence of the positive integers such that $\lim _{k \rightarrow \infty}\left(a_{n_k}+\right.$ $\left.b_{n_k}\right)=\limsup _{n \rightarrow \infty}\left(a_n+b_n\right)$. Then choose a subsequence of the positive integers $\left\{k_m\right\}$ such that
$$
\lim _{m \rightarrow \infty} a_{n_{k_m}}=\limsup _{k \rightarrow \infty} a_{n_k} .
$$
The subsequence $a_{n_{k_m}}+b_{n_{k_m}}$ still converges to the same limit as $a_{n_k}+b_{n_k}$, i.e., to $\limsup _{n \rightarrow \infty}\left(a_n+b_n\right)$. Hence, since $a_{n_k}$ is bounded above (so that $\limsup _{k \rightarrow \infty} a_{n_k}$ is finite), it follows that $b_{n_{k_m}}$ converges to the difference
$$
\lim _{m \rightarrow \infty} b_{n_{k_m}}=\lim _{m \rightarrow \infty}\left(a_{n_{k_m}}+b_{n_{k_m}}\right)-\lim _{m \rightarrow \infty} a_{n_{k_m}} .
$$
Thus we have proved that there exist subsequences $\left\{a_{n_{k_m}}\right\}$ and $\left\{b_{n_{k_m}}\right\}$ which converge to limits $a$ and $b$ respectively such that $a+b=\limsup _{n \rightarrow \infty}\left(a_n+b_n^*\right)$. Since $a$ is the limit of a subsequence of $\left\{a_n\right\}$ and $b$ is the limit of a subsequence of $\left\{b_n\right\}$, it follows that $a \leq \limsup _{n \rightarrow \infty} a_n$ and $b \leq \limsup _{n \rightarrow \infty} b_n$, from which the desired inequality follows.
-/

theorem Rudin_exercise_3_5
    (a b : ℕ → EReal)
    (hareal : ∀ n, a n ≠ ⊤ ∧ a n ≠ ⊥)
    (hbreal : ∀ n, b n ≠ ⊤ ∧ b n ≠ ⊥)
    (ha : limsup a ≠ ⊤)
    (hb : limsup b ≠ ⊥) :
    limsup (λ n => a n + b n) ≤ limsup a + limsup b := by
  sorry

/-
The previous formal statement is false.  The sequences
`aₙ = -n` and `bₙ = n`, viewed inside `EReal`, satisfy all of the stated
hypotheses, yet they give `limsup (aₙ + bₙ) = 0` while
`limsup aₙ + limsup bₙ = ⊥`.  The inequality therefore fails because the
right-hand side collapses to `⊥`, even though the sum of the lim sups is meant
to avoid the indeterminate form `-∞ + +∞`.  To repair the argument we must also
exclude the case `limsup aₙ = ⊥ ∧ limsup bₙ = ⊤`.
-/

namespace Proofnet343

def seq343A (n : ℕ) : EReal :=
  (-(n : ℝ) : EReal)

def seq343B (n : ℕ) : EReal :=
  (n : ℝ)

@[simp] lemma seq343A_add_seq343B (n : ℕ) :
    seq343A n + seq343B n = (0 : EReal) := by
  -- Step 1: Unfold both sequences so that the expression is entirely written in terms of `ℝ`.
  -- Step 2: Rely on the fact that addition inside `EReal` agrees with addition of reals whenever both summands are finite.
  have hreal : (-(n : ℝ)) + (n : ℝ) = (0 : ℝ) := by
    -- Step 1.1: This is the classical identity `-x + x = 0`.
    simp
  have hrealE :
      ((-(n : ℝ)) + (n : ℝ) : EReal) = (0 : EReal) := by
    -- Step 1.2: Coerce the real equality into `EReal`.
    exact_mod_cast hreal
  -- Step 2.1: Rewrite the target using the auxiliary equality.
  simpa [seq343A, seq343B] using hrealE

lemma seq343A_finite : ∀ n, seq343A n ≠ ⊤ ∧ seq343A n ≠ ⊥ := by
  -- Step 1: Expose the definition of `seq343A` so that `simp` can detect it is a real number.
  -- Step 2: Apply the basic `simp` rules that prohibit real points of `EReal` from coinciding with `⊤` or `⊥`.
  intro n
  constructor
  · -- Step 2.1: Real points never equal `⊤`.
    simpa [seq343A] using (EReal.coe_ne_top (-(n : ℝ)))
  · -- Step 2.2: Real points never equal `⊥`.
    simpa [seq343A] using (EReal.coe_ne_bot (-(n : ℝ)))

lemma seq343B_finite : ∀ n, seq343B n ≠ ⊤ ∧ seq343B n ≠ ⊥ := by
  -- Step 1: Again reduce to a statement purely about real numbers.
  -- Step 2: Finish by the same `simp` facts about the coercion into `EReal`.
  intro n
  constructor
  · -- Step 2.1: Coercions of real numbers never hit `⊤`.
    simpa [seq343B] using (EReal.coe_ne_top (n : ℝ))
  · -- Step 2.2: Coercions of real numbers never hit `⊥`.
    simpa [seq343B] using (EReal.coe_ne_bot (n : ℝ))

lemma eventually_seq343A_lt {y : EReal} (hy : (⊥ : EReal) < y) :
    ∀ᶠ n : ℕ in atTop, seq343A n < y := by
  -- Step 1: Perform case analysis on `y` with `EReal.rec`, treating ⊥, real values, and ⊤ separately.
  revert hy
  refine
    (EReal.rec
        (motive := fun y => (⊥ : EReal) < y → ∀ᶠ n : ℕ in atTop, seq343A n < y)
        ?botCase ?realCase ?topCase y)
  · -- Step 1.1: The case `y = ⊥` contradicts the assumption `⊥ < y`.
    intro hy
    exact (lt_irrefl _ hy).elim
  · -- Step 1.2: For `y = r : ℝ`, make `-r` a threshold beyond which all terms lie below `r`.
    intro r _
    -- Step 1.2.1: Pick a natural number larger than `-r`.
    obtain ⟨N, hN⟩ := exists_nat_gt (-r)
    -- Step 1.2.2: Use the `eventually_atTop` characterization to enforce the required inequality past `N`.
    refine (Filter.eventually_atTop.2 ⟨N, ?_⟩)
    intro n hn
    -- Step 1.2.3: Convert the inequalities to the real line and flip them using `neg_lt_neg_iff`.
    have hlt₁ : (-r : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hle : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlt₂ : (-r : ℝ) < (n : ℝ) := lt_of_lt_of_le hlt₁ hle
    have hreal : (-(n : ℝ)) < r := by
      simpa [neg_neg] using (neg_lt_neg_iff.mpr hlt₂)
    -- Step 1.2.4: Translate the real inequality back to `EReal`.
    have hrealE : ((-(n : ℝ)) : EReal) < (r : EReal) := by
      -- Step 1.2.4.1: Coerce both sides into `EReal`.
      exact_mod_cast hreal
    simpa [seq343A] using hrealE
  · -- Step 1.3: If `y = ⊤`, the claim is immediate because finite values are always strictly below ⊤.
    intro _
    exact Filter.Eventually.of_forall fun n => by
      simpa [seq343A] using (EReal.coe_lt_top (-(n : ℝ)))

lemma frequently_seq343B_gt {y : EReal} (hy : y < (⊤ : EReal)) :
    ∃ᶠ n : ℕ in atTop, y < seq343B n := by
  -- Step 1: Again reason by cases on `y` using `EReal.rec`.
  revert hy
  refine
    (EReal.rec
        (motive := fun y => y < (⊤ : EReal) → ∃ᶠ n : ℕ in atTop, y < seq343B n)
        ?botCase ?realCase ?topCase y)
  · -- Step 1.1: When `y = ⊥`, the desired inequality holds for all indices, hence frequently.
    intro _
    exact (Filter.Eventually.of_forall fun n => by
      simpa [seq343B] using (EReal.bot_lt_coe (n : ℝ))).frequently
  · -- Step 1.2: For `y = r : ℝ`, eventually every natural number dominates `r`.
    intro r _
    -- Step 1.2.1: Choose a natural number strictly larger than `r`.
    obtain ⟨N, hN⟩ := exists_nat_gt r
    -- Step 1.2.2: Encode the eventual inequality on ℕ via `eventually_atTop`.
    have hEvent :
        ∀ᶠ n : ℕ in atTop, (r : EReal) < seq343B n := by
      refine (Filter.eventually_atTop.2 ⟨N, ?_⟩)
      intro n hn
      have hlt₁ : (r : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hle : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hreal : (r : ℝ) < (n : ℝ) := lt_of_lt_of_le hlt₁ hle
      -- Step 1.2.2.1: Coerce the inequality into `EReal`.
      have hrealE : (r : EReal) < ((n : ℝ) : EReal) := by exact_mod_cast hreal
      simpa [seq343B] using hrealE
    -- Step 1.2.3: Promote the eventual statement to a frequent one.
    exact hEvent.frequently
  · -- Step 1.3: The case `y = ⊤` contradicts `y < ⊤`.
    intro hy
    exact (lt_irrefl _ hy).elim

lemma limsup_seq343A_eq_bot : limsup seq343A = (⊥ : EReal) := by
  -- Step 1: Show that `limsup seq343A ≤ ⊥` using the characterization from `limsup_le_iff`.
  have hle :
      limsup seq343A ≤ (⊥ : EReal) := by
    -- Step 1.1: Reformulate the inequality by providing the required eventual strict bounds.
    refine (limsup_le_iff (u := seq343A) (f := Filter.atTop)).2 ?_
    -- Step 1.2: Invoke the previously established eventual inequality `eventually_seq343A_lt`.
    intro y hy
    exact eventually_seq343A_lt hy
  -- Step 2: Combine this with the trivial lower bound `⊥ ≤ limsup seq343A`.
  exact le_antisymm hle bot_le

lemma limsup_seq343B_eq_top : limsup seq343B = (⊤ : EReal) := by
  -- Step 1: Use `le_limsup_iff` to prove `⊤ ≤ limsup seq343B`.
  have hge :
      (⊤ : EReal) ≤ limsup seq343B := by
    refine (le_limsup_iff (u := seq343B) (f := Filter.atTop)).2 ?_
    intro y hy
    exact frequently_seq343B_gt hy
  -- Step 2: Symmetrically, `limsup seq343B ≤ ⊤` is automatic, giving the desired equality.
  exact le_antisymm le_top hge

lemma limsup_seq343_sum :
    limsup (fun n => seq343A n + seq343B n) = (0 : EReal) := by
  -- Step 1: Observe that every term of the sequence is exactly `0`.
  have hconst :
      (fun n => seq343A n + seq343B n) = fun _ : ℕ => (0 : EReal) := by
    -- Step 1.1: Establish pointwise equality by unfolding both definitions.
    funext n
    simp [seq343A_add_seq343B]
  -- Step 2: Apply the lemma `limsup_const` to conclude.
  simp

theorem Rudin_exercise_3_5_neg :
    ¬ (∀ (a b : ℕ → EReal)
        (_hareal : ∀ n, a n ≠ ⊤ ∧ a n ≠ ⊥)
        (_hbreal : ∀ n, b n ≠ ⊤ ∧ b n ≠ ⊥)
        (_ha : limsup a ≠ ⊤)
        (_hb : limsup b ≠ ⊥),
        limsup (fun n => a n + b n) ≤ limsup a + limsup b) := by
  -- Step 1: Assume the universally quantified implication and specialize it to our counterexample sequences.
  intro h
  have hareal := seq343A_finite
  have hbreal := seq343B_finite
  have ha : limsup seq343A ≠ ⊤ := by
    -- Step 1.1: Rewrite the `limsup` value using the computed equality.
    simp [limsup_seq343A_eq_bot]
  have hb : limsup seq343B ≠ ⊥ := by
    -- Step 1.2: Similarly compute the `limsup` of `seq343B`.
    simp [limsup_seq343B_eq_top]
  have hineq :=
      h seq343A seq343B hareal hbreal ha hb
  -- Step 2: Unfold each `limsup` in the inequality to see the impossible comparison.
  have hfalse :
      (0 : EReal) ≤ (⊥ : EReal) := by
    simp [limsup_seq343A_eq_bot, limsup_seq343B_eq_top] at hineq
  -- Step 3: Derive the contradiction `0 ≤ ⊥` ⇒ `False` from the fact that `⊥ < 0`.
  exact (not_le_of_gt (EReal.bot_lt_coe (0 : ℝ))) hfalse

/-
The original formalization is not faithful to the informal statement for two reasons:

1. **Wrong hypotheses (making it false):** The original imposes `ha : limsup a ≠ ⊤` and
   `hb : limsup b ≠ ⊥`, which only excludes the indeterminate form (+∞) + (−∞) while
   missing (−∞) + (+∞). The counterexample above (aₙ = −n, bₙ = n) exploits this gap.

2. **Stronger domain (ℕ → EReal vs ℕ → ℝ):** The informal says "real sequences," meaning
   `a b : ℕ → ℝ`. The original uses `ℕ → EReal`, allowing sequences to take ±∞ pointwise,
   which is a strict generalization. In standard real analysis (Rudin), sequences are
   real-valued; only the limsup itself can be ±∞.

The correction uses `a b : ℕ → ℝ`, coerces to EReal for the limsup/addition, and imposes
the minimal pair of disjunctions that exactly captures "the right-hand side is not of the
form ∞ − ∞":
  • `limsup (↑a) ≠ ⊥ ∨ limsup (↑b) ≠ ⊤` — excludes (−∞) + (+∞)
  • `limsup (↑a) ≠ ⊤ ∨ limsup (↑b) ≠ ⊥` — excludes (+∞) + (−∞)
-/

theorem Rudin_exercise_3_5_corrected
    (a b : ℕ → ℝ)
    (h1 : limsup (fun n => (a n : EReal)) ≠ ⊥ ∨ limsup (fun n => (b n : EReal)) ≠ ⊤)
    (h2 : limsup (fun n => (a n : EReal)) ≠ ⊤ ∨ limsup (fun n => (b n : EReal)) ≠ ⊥) :
    limsup (fun n => ((a n + b n : ℝ) : EReal)) ≤
      limsup (fun n => (a n : EReal)) + limsup (fun n => (b n : EReal)) := by
  -- Step 1: Rewrite the LHS to use pointwise EReal addition, since (↑(a + b)) = (↑a) + (↑b).
  have hcast : (fun n => ((a n + b n : ℝ) : EReal)) = (fun n => (a n : EReal) + (b n : EReal)) := by
    funext n; exact_mod_cast rfl
  rw [hcast]
  -- Step 2: Apply Mathlib's `EReal.limsup_add_le`.
  exact EReal.limsup_add_le h1 h2

end Proofnet343
