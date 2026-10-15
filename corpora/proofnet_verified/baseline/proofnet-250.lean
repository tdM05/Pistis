import Mathlib

open Fintype Subgroup Set Polynomial Ideal MvPolynomial
open scoped BigOperators

/-Informal Statement

Prove that the ring $\mathbb{Z}\left[x_{1}, x_{2}, x_{3}, \ldots\right] /\left(x_{1} x_{2}, x_{3} x_{4}, x_{5} x_{6}, \ldots\right)$ contains infinitely many minimal prime ideals.
-/

/-Informal Proof

Let $R=\mathbb{Z}\left[x_1, x_2, \ldots, x_n\right]$ and consider the ideal $K=\left(x_{2 k+1} x_{2 k+2} \mid k \in \mathbb{Z}_{+}\right)$in $R$.
Consider the family of subsets $X=\left\{\left\{x_{2 k+1}, x_{2 k+2}\right\} \mid k \in \mathbb{Z}_{+}\right\}$, and $Y$ the set of choice function on $X$, ie the set of functions $\lambda: \mathbb{Z}_{+} \rightarrow \cup_{\mathbb{Z}_{+}}\left\{x_{2 k+1}, x_{2 k+2}\right\}$ with $\lambda(a) \in$ $\left\{x_{2 a+1}, x_{2 a+2}\right\}$
For each $\lambda \in Y$ we have the ideal $I_\lambda=(\lambda(0), \lambda(1), \ldots)$.
All these ideals are distinct, ie for $\lambda \neq \lambda^{\prime}$ we have $I_\lambda \neq I_{\lambda^{\prime}}$.
We also have that by construction $K \subset I_\lambda$ for all $\lambda \in Y$.
By the Third Isomorphism Theorem
$$
(R / K) /\left(I_\lambda / K\right) \cong R / I_\lambda
$$
Note also that $R / I_\lambda$ is isomorphic to the polynomial ring over $R$ with indeterminates the $x_i$ not in the image of $\lambda$, and since there is a countably infinite number of them we can conclude $R / I_\lambda \cong R$, an integral domain. Therefore $I_\lambda / K$ is a prime ideal of $R / K$

We prove now that $I_\lambda / K$ is a minimal prime ideal. Let $J / K \subseteq I_\lambda / K$ be a prime ideal. For each pair $\left(x_{2 k+1}, x_{2 k+2}\right)$ we have that $x_{2 k+1} x_{2 k+2} \in K$ so $x_{2 k+1} x_{2 k+2} \bmod K \in J / K$ so $J$ must contain one of the elements in $\left\{x_{2 k+1}, x_{2 k+2}\right\}$. But since $J / K \subseteq I_\lambda / K$ it must be $\lambda(k)$ for all $k \in \mathbb{Z}_{+}$. Therefore $J / K=I_\lambda / K$
-/

/-
FORMAL PROOF STRATEGY:
=======================

We prove the statement by constructing an infinite family of distinct minimal prime ideals.

For each n : ℕ, we construct a prime ideal P_n in MvPolynomial ℕ ℤ as:
  P_n = span { X_{2i} : i ≠ n } ∪ { X_{2n+1} }

That is, P_n contains all even-indexed variables except X_{2n}, plus the odd variable X_{2n+1}.

Key properties we prove:
1. I ≤ P_n for all n, where I = span { X_{2i} · X_{2i+1} : i ∈ ℕ }
   (because for each pair, either X_{2i} ∈ P_n (if i ≠ n) or X_{2i+1} ∈ P_n (if i = n))

2. P_n is prime
   (we construct a substitution map φ_n that kills P_n and maps to a domain)

3. P_n is minimal among primes containing I
   (if Q ⊆ P_n is prime containing I, then for each pair either X_{2i} ∈ Q or X_{2i+1} ∈ Q,
    and by primeness + containment in P_n, we can determine exactly which, forcing Q = P_n)

4. P_n ≠ P_m for n ≠ m
   (because X_{2n} ∉ P_n but X_{2n} ∈ P_m for m ≠ n)

This gives infinitely many minimal primes over I, hence infinitely many minimal primes
in the quotient ring R/I via the correspondence minimalPrimes(R/I) ↔ I.minimalPrimes.
-/

-- ============================================================================
-- STEP 1: Define the choice function and index set for ideal P_n
-- ============================================================================

/-- For ideal P_n, we select variable X_{choice n i} from the i-th pair (X_{2i}, X_{2i+1}).
    If i = n, we choose X_{2n+1} (the odd one), otherwise we choose X_{2i} (the even one). -/
def choice (n i : ℕ) : ℕ := if i = n then 2*n + 1 else 2*i

/-- The set of variable indices in ideal P_n -/
def Pidx (n : ℕ) : Set ℕ := range (choice n)

/-- The prime ideal P_n = span { X_k : k ∈ Pidx n } -/
def P' (n : ℕ) : Ideal (MvPolynomial ℕ ℤ) := span (MvPolynomial.X '' Pidx n)

-- ============================================================================
-- STEP 2: Basic membership lemmas for P'
-- ============================================================================

/-- A variable X_k is in P' n iff k is in Pidx n -/
lemma X_mem_P' (n k : ℕ) (hk : k ∈ Pidx n) : (MvPolynomial.X k : MvPolynomial ℕ ℤ) ∈ P' n := by
  unfold P'
  apply subset_span
  exact ⟨k, hk, rfl⟩

/-- Each product X_{2i} · X_{2i+1} is in P' n for any n -/
lemma prod_mem_P' (n i : ℕ) : (MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1) : MvPolynomial ℕ ℤ) ∈ P' n := by
  -- Split on whether i = n or not
  by_cases hi : i = n
  · -- Case i = n: X_{2n+1} ∈ P_n, so the product is in P_n via left multiplication
    have h : (2*i + 1) ∈ Pidx n := by
      unfold Pidx choice; simp only [mem_range]; use i; simp [hi]
    exact Ideal.mul_mem_left _ _ (X_mem_P' n (2*i+1) h)
  · -- Case i ≠ n: X_{2i} ∈ P_n, so the product is in P_n via right multiplication
    have h : (2*i) ∈ Pidx n := by
      unfold Pidx choice; simp only [mem_range]; use i; simp [hi]
    exact Ideal.mul_mem_right _ _ (X_mem_P' n (2*i) h)

/-- The ideal I = span{f(i)} is contained in P' n for all n -/
lemma I_le_P' {f : ℕ → MvPolynomial ℕ ℤ}
    (hf : f = fun i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)) (n : ℕ) :
    span (range f) ≤ P' n := by
  rw [span_le]
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  rw [hf]
  exact prod_mem_P' n i

-- ============================================================================
-- STEP 3: Show 2n ∉ Pidx n (critical for distinguishing P_n from P_m)
-- ============================================================================

/-- 2n is NOT in Pidx n (i.e., X_{2n} ∉ P_n) -/
lemma two_n_not_in_Pidx (n : ℕ) : 2*n ∉ Pidx n := by
  unfold Pidx choice
  simp only [mem_range, not_exists]
  intro i
  -- For any i: if i = n then choice n i = 2n+1 ≠ 2n; if i ≠ n then choice n i = 2i ≠ 2n
  by_cases hi : i = n
  · simp only [hi, ↓reduceIte]; omega
  · simp only [hi, ↓reduceIte]; omega

/-- 2n IS in Pidx m when m ≠ n (i.e., X_{2n} ∈ P_m for m ≠ n) -/
lemma two_n_in_Pidx_of_ne (n m : ℕ) (h : m ≠ n) : 2*n ∈ Pidx m := by
  unfold Pidx choice
  simp only [mem_range]
  use n
  simp [h.symm]

-- ============================================================================
-- STEP 4: Define decidable membership and the substitution map φ
-- ============================================================================

/-- Decidable version of membership in Pidx n -/
def inPidx (n k : ℕ) : Bool :=
  (k % 2 = 0 ∧ k / 2 ≠ n) ∨ k = 2*n + 1

/-- Equivalence between decidable and set membership -/
lemma inPidx_iff (n k : ℕ) : inPidx n k = true ↔ k ∈ Pidx n := by
  unfold inPidx Pidx choice
  simp only [mem_range, decide_eq_true_eq]
  constructor
  · intro h
    rcases h with ⟨heven, hne⟩ | heq
    · use k / 2
      have hkdiv : k / 2 ≠ n := hne
      simp only [hkdiv, ↓reduceIte]
      omega
    · use n
      simp only [↓reduceIte, heq]
  · intro ⟨i, hi⟩
    by_cases heq : i = n
    · right; simp only [heq, ↓reduceIte] at hi; exact hi.symm
    · left; simp only [heq, ↓reduceIte] at hi; subst hi
      constructor
      · omega
      · have : 2 * i / 2 = i := Nat.mul_div_cancel_left i (by omega : 0 < 2)
        rw [this]; exact heq

/-- The substitution: send X_k to 0 if k ∈ Pidx n, otherwise keep X_k -/
noncomputable def subst (n : ℕ) : ℕ → MvPolynomial ℕ ℤ :=
  fun k => if inPidx n k then 0 else MvPolynomial.X k

/-- The ring homomorphism φ_n: kills variables in Pidx n, preserves others -/
noncomputable def φ (n : ℕ) : MvPolynomial ℕ ℤ →ₐ[ℤ] MvPolynomial ℕ ℤ :=
  MvPolynomial.aeval (subst n)

/-- φ sends variables in Pidx n to 0 -/
lemma φ_X_zero (n k : ℕ) (hk : k ∈ Pidx n) : φ n (MvPolynomial.X k) = 0 := by
  unfold φ
  rw [MvPolynomial.aeval_X]
  unfold subst
  rw [← inPidx_iff] at hk
  simp [hk]

/-- φ preserves variables not in Pidx n -/
lemma φ_X_self (n k : ℕ) (hk : k ∉ Pidx n) : φ n (MvPolynomial.X k) = MvPolynomial.X k := by
  unfold φ
  rw [MvPolynomial.aeval_X]
  unfold subst
  have : inPidx n k = false := by rw [← Bool.not_eq_true, inPidx_iff]; exact hk
  simp [this]

-- ============================================================================
-- STEP 5: Show elements of P' n map to 0 under φ
-- ============================================================================

/-- Elements of P' n are killed by φ_n -/
lemma φ_zero_on_P' (n : ℕ) (x : MvPolynomial ℕ ℤ) (hx : x ∈ P' n) : φ n x = 0 := by
  unfold P' at hx
  -- Induct on the span structure
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk, rfl⟩ := hy
    exact φ_X_zero n k hk
  | zero => simp [φ, map_zero]
  | add a b _ _ ha hb => simp only [map_add, ha, hb, add_zero]
  | smul r a _ ha => simp only [smul_eq_mul, map_mul, ha, mul_zero]

/-- The kernel of φ contains P' n -/
lemma P'_le_ker_φ (n : ℕ) : P' n ≤ RingHom.ker (φ n).toRingHom := by
  intro x hx
  rw [RingHom.mem_ker]
  exact φ_zero_on_P' n x hx

-- ============================================================================
-- STEP 6: Show X_{2n} ∉ P' n using evaluation
-- ============================================================================

/-- X_{2n} is NOT in P' n - proved using evaluation to ℤ -/
lemma X_two_n_not_mem_P' (n : ℕ) : (MvPolynomial.X (2*n) : MvPolynomial ℕ ℤ) ∉ P' n := by
  intro h
  have h2n : 2*n ∉ Pidx n := two_n_not_in_Pidx n
  -- Define evaluation: X_{2n} ↦ 1, all others ↦ 0
  let ev : ℕ → ℤ := fun k => if k = 2*n then 1 else 0
  -- X_{2n} evaluates to 1
  have hev : MvPolynomial.aeval ev (MvPolynomial.X (2*n) : MvPolynomial ℕ ℤ) = 1 := by
    rw [MvPolynomial.aeval_X]; exact if_pos rfl
  -- Variables in Pidx n evaluate to 0 (since 2n ∉ Pidx n, so k ≠ 2n for k ∈ Pidx n)
  have hgen : ∀ k ∈ Pidx n, MvPolynomial.aeval ev (MvPolynomial.X k : MvPolynomial ℕ ℤ) = 0 := by
    intro k hk
    rw [MvPolynomial.aeval_X]
    have hne : k ≠ 2*n := fun heq => h2n (heq ▸ hk)
    exact if_neg hne
  -- Everything in P' n evaluates to 0
  have hP' : ∀ x ∈ P' n, MvPolynomial.aeval ev x = 0 := by
    intro x hx
    unfold P' at hx
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨k, hk, rfl⟩ := hy; exact hgen k hk
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add, ha, hb, add_zero]
    | smul r a _ ha => simp only [smul_eq_mul, map_mul, ha, mul_zero]
  -- But X_{2n} ∈ P' n would mean 1 = 0, contradiction
  have := hP' (MvPolynomial.X (2*n)) h
  rw [hev] at this
  exact one_ne_zero this

/-- X_{2n} IS in P' m when m ≠ n -/
lemma X_two_n_mem_P'_of_ne (n m : ℕ) (h : m ≠ n) : (MvPolynomial.X (2*n) : MvPolynomial ℕ ℤ) ∈ P' m := by
  have hk : 2*n ∈ Pidx m := two_n_in_Pidx_of_ne n m h
  exact X_mem_P' m (2*n) hk

-- ============================================================================
-- STEP 7: Prove P' is injective (P_n ≠ P_m for n ≠ m)
-- ============================================================================

/-- P' is injective: different n give different ideals -/
lemma P'_injective : Function.Injective P' := by
  intro n m h
  by_contra hne
  -- X_{2n} ∈ P' m (since m ≠ n)
  have hmem : (MvPolynomial.X (2*n) : MvPolynomial ℕ ℤ) ∈ P' m := X_two_n_mem_P'_of_ne n m (Ne.symm hne)
  -- But P' n = P' m, so X_{2n} ∈ P' n, contradicting X_two_n_not_mem_P'
  rw [← h] at hmem
  exact X_two_n_not_mem_P' n hmem

-- ============================================================================
-- STEP 8: Membership characterizations for odd variables
-- ============================================================================

/-- X_{2i+1} ∉ P' n when i ≠ n -/
lemma X_odd_not_mem_P'_of_ne (n i : ℕ) (hne : i ≠ n) : (MvPolynomial.X (2*i+1) : MvPolynomial ℕ ℤ) ∉ P' n := by
  intro h
  -- 2i+1 ∉ Pidx n when i ≠ n
  have hnotin : 2*i+1 ∉ Pidx n := by
    unfold Pidx choice; simp only [mem_range, not_exists]; intro j
    by_cases hj : j = n
    · simp only [hj, ↓reduceIte]; intro heq; exact hne (by omega : i = n)
    · simp only [hj, ↓reduceIte]; omega
  -- Use evaluation X_{2i+1} ↦ 1, others ↦ 0
  let ev : ℕ → ℤ := fun k => if k = 2*i+1 then 1 else 0
  have hev : MvPolynomial.aeval ev (MvPolynomial.X (2*i+1) : MvPolynomial ℕ ℤ) = 1 := by
    rw [MvPolynomial.aeval_X]; exact if_pos rfl
  have hgen : ∀ k ∈ Pidx n, MvPolynomial.aeval ev (MvPolynomial.X k : MvPolynomial ℕ ℤ) = 0 := by
    intro k hk; rw [MvPolynomial.aeval_X]
    have hne' : k ≠ 2*i+1 := fun heq => hnotin (heq ▸ hk)
    exact if_neg hne'
  have hP' : ∀ x ∈ P' n, MvPolynomial.aeval ev x = 0 := by
    intro x hx; unfold P' at hx
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨k, hk, rfl⟩ := hy; exact hgen k hk
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add, ha, hb, add_zero]
    | smul r a _ ha => simp only [smul_eq_mul, map_mul, ha, mul_zero]
  have := hP' (MvPolynomial.X (2*i+1)) h
  rw [hev] at this
  exact one_ne_zero this

/-- X_{2n+1} IS in P' n -/
lemma X_odd_mem_P'_of_eq (n : ℕ) : (MvPolynomial.X (2*n+1) : MvPolynomial ℕ ℤ) ∈ P' n := by
  have : 2*n+1 ∈ Pidx n := by unfold Pidx choice; simp only [mem_range]; use n; simp
  exact X_mem_P' n (2*n+1) this

-- ============================================================================
-- STEP 9: Prove P' n ≠ ⊤
-- ============================================================================

/-- P' n is a proper ideal -/
lemma P'_ne_top (n : ℕ) : P' n ≠ ⊤ := by
  intro h
  -- If P' n = ⊤, then 1 ∈ P' n
  have : (1 : MvPolynomial ℕ ℤ) ∈ P' n := by rw [h]; trivial
  -- But evaluating at all 0s: 1 ↦ 1, everything in P' n ↦ 0
  let ev : ℕ → ℤ := fun _ => 0
  have hev : MvPolynomial.aeval ev (1 : MvPolynomial ℕ ℤ) = 1 := by simp only [map_one]
  have hP' : ∀ x ∈ P' n, MvPolynomial.aeval ev x = 0 := by
    intro x hx; unfold P' at hx
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨k, hk, rfl⟩ := hy; rw [MvPolynomial.aeval_X]
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add, ha, hb, add_zero]
    | smul r a _ ha => simp only [smul_eq_mul, map_mul, ha, mul_zero]
  have := hP' 1 this
  rw [hev] at this
  exact one_ne_zero this

-- ============================================================================
-- STEP 10: Key lemma for primality: p - φ p ∈ P' n for all p
-- ============================================================================

/-- p - φ_n(p) ∈ P' n for all polynomials p.
    This captures that φ_n is the "projection" modulo P' n. -/
lemma sub_φ_mem_P' (n : ℕ) (p : MvPolynomial ℕ ℤ) : p - φ n p ∈ P' n := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    -- Constants: φ(c) = c, so c - c = 0 ∈ P' n
    simp [φ]
  | add p' q' hp' hq' =>
    -- Addition: (p + q) - φ(p + q) = (p - φ p) + (q - φ q)
    simp only [map_add]
    have heq : p' + q' - (φ n p' + φ n q') = (p' - φ n p') + (q' - φ n q') := by ring
    rw [heq]
    exact Ideal.add_mem _ hp' hq'
  | mul_X p' i hp' =>
    -- Multiplication by X_i
    simp only [map_mul]
    by_cases hi : i ∈ Pidx n
    · -- X_i ∈ Pidx n: φ(X_i) = 0, so p * X_i - 0 = p * X_i ∈ P' n
      have hXi : (MvPolynomial.X i : MvPolynomial ℕ ℤ) ∈ P' n := X_mem_P' n i hi
      have hmem : p' * MvPolynomial.X i ∈ P' n := Ideal.mul_mem_left _ _ hXi
      simp only [φ_X_zero n i hi, mul_zero, sub_zero]
      exact hmem
    · -- X_i ∉ Pidx n: φ(X_i) = X_i, so p*X_i - φ(p)*X_i = (p - φ(p))*X_i ∈ P' n
      simp only [φ_X_self n i hi]
      have heq : p' * MvPolynomial.X i - φ n p' * MvPolynomial.X i
               = (p' - φ n p') * MvPolynomial.X i := by ring
      rw [heq]
      exact Ideal.mul_mem_right _ _ hp'

-- ============================================================================
-- STEP 11: Prove P' n is prime
-- ============================================================================

/-- P' n is a prime ideal.
    Key insight: φ_n maps to a domain (MvPolynomial ℕ ℤ itself), and ker(φ_n) = P' n.
    If p*q ∈ P' n, then φ(p)*φ(q) = 0, so φ(p) = 0 or φ(q) = 0.
    Using p - φ(p) ∈ P' n, we get p ∈ P' n or q ∈ P' n. -/
lemma P'_isPrime (n : ℕ) : (P' n).IsPrime := by
  constructor
  · exact P'_ne_top n
  · intro p q hpq
    -- φ(p) * φ(q) = 0 in the domain MvPolynomial ℕ ℤ
    have h : φ n p * φ n q = 0 := by
      rw [← map_mul]
      exact φ_zero_on_P' n (p * q) hpq
    -- In a domain, if ab = 0 then a = 0 or b = 0
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h with hp0 | hq0
    · -- φ(p) = 0, so p = p - 0 = p - φ(p) ∈ P' n
      left
      have hdiff : p - φ n p ∈ P' n := sub_φ_mem_P' n p
      rw [hp0] at hdiff
      simp at hdiff
      exact hdiff
    · -- φ(q) = 0, so q ∈ P' n by same argument
      right
      have hdiff : q - φ n q ∈ P' n := sub_φ_mem_P' n q
      rw [hq0] at hdiff
      simp at hdiff
      exact hdiff

-- ============================================================================
-- STEP 12: Prove P' n is minimal among primes containing I
-- ============================================================================

/-- P' n is minimal: any prime Q with I ≤ Q ≤ P' n must equal P' n.
    The proof uses that Q must contain one variable from each pair (X_{2i}, X_{2i+1}),
    and containment in P' n forces the "right" choice. -/
lemma P'_minimal (n : ℕ) {Q : Ideal (MvPolynomial ℕ ℤ)}
    (hQ_prime : Q.IsPrime)
    (hI_le : span (range (fun i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1) : ℕ → MvPolynomial ℕ ℤ)) ≤ Q)
    (hQ_le : Q ≤ P' n) : Q = P' n := by
  apply le_antisymm hQ_le
  -- Show P' n ⊆ Q by checking generators
  rw [P', span_le]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := hx
  unfold Pidx at hk; obtain ⟨i, rfl⟩ := hk
  unfold choice
  by_cases hi : i = n
  · -- i = n: need to show X_{2n+1} ∈ Q
    simp only [hi, ↓reduceIte]
    -- The product X_{2n} · X_{2n+1} ∈ Q
    have hprod : (MvPolynomial.X (2*n) * MvPolynomial.X (2*n+1) : MvPolynomial ℕ ℤ) ∈ Q := by
      apply hI_le; apply subset_span; simp only [mem_range]; use n
    -- By primeness, X_{2n} ∈ Q or X_{2n+1} ∈ Q
    rcases hQ_prime.mem_or_mem hprod with h2n | h2n1
    · -- X_{2n} ∈ Q would mean X_{2n} ∈ P' n (via Q ≤ P' n), contradicting X_two_n_not_mem_P'
      exfalso; exact X_two_n_not_mem_P' n (hQ_le h2n)
    · exact h2n1
  · -- i ≠ n: need to show X_{2i} ∈ Q
    simp only [hi, ↓reduceIte]
    have hprod : (MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1) : MvPolynomial ℕ ℤ) ∈ Q := by
      apply hI_le; apply subset_span; simp only [mem_range]; use i
    rcases hQ_prime.mem_or_mem hprod with h2i | h2i1
    · exact h2i
    · -- X_{2i+1} ∈ Q would mean X_{2i+1} ∈ P' n, contradicting X_odd_not_mem_P'_of_ne
      exfalso; exact X_odd_not_mem_P'_of_ne n i hi (hQ_le h2i1)

-- ============================================================================
-- STEP 13: Show P' n is a minimal prime over I
-- ============================================================================

/-- P' n is in the set of minimal primes over I -/
lemma P'_mem_minimalPrimes (n : ℕ) {f : ℕ → MvPolynomial ℕ ℤ}
    (hf : f = fun i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)) :
    P' n ∈ (span (range f)).minimalPrimes := by
  rw [Ideal.minimalPrimes]
  simp only [Set.mem_setOf_eq, Minimal]
  constructor
  · constructor
    · exact P'_isPrime n
    · exact I_le_P' hf n
  · intro Q ⟨hQ_prime, hI_le⟩ hQ_le
    exact (P'_minimal n hQ_prime (hf ▸ hI_le) hQ_le).symm ▸ le_refl _

-- ============================================================================
-- STEP 14: Main theorem - infinitely many minimal primes
-- ============================================================================

/-- Main theorem: there are infinitely many minimal primes in the quotient ring.
    We use the correspondence between minimal primes of R/I and minimal primes over I in R. -/
theorem Dummit_Foote_exercise_9_1_10 {f : ℕ → MvPolynomial ℕ ℤ}
    (hf : f = fun i => MvPolynomial.X (2*i) * MvPolynomial.X (2*i+1)) :
    Infinite (minimalPrimes (MvPolynomial ℕ ℤ ⧸ span (range f))) := by
  -- P' is injective, so gives infinitely many distinct ideals
  have hinj : Function.Injective (fun n => P' n) := P'_injective
  -- Each P' n is a minimal prime over I
  have hmem : ∀ n, P' n ∈ (span (range f)).minimalPrimes := fun n => P'_mem_minimalPrimes n hf
  -- The set of minimal primes over I is infinite
  have hI_inf : Set.Infinite ((span (range f)).minimalPrimes) := by
    apply Set.infinite_of_injective_forall_mem hinj hmem
  -- Use the bijection: I.minimalPrimes = comap (Quotient.mk I) '' minimalPrimes (R ⧸ I)
  have hbij := Ideal.minimalPrimes_eq_comap (I := span (range f))
  rw [hbij] at hI_inf
  -- The comap of quotient is injective, so if the image is infinite, so is the source
  rw [Set.infinite_coe_iff]
  have hcomap_inj : Function.Injective (Ideal.comap (Ideal.Quotient.mk (span (range f)))) :=
    Ideal.comap_injective_of_surjective (Ideal.Quotient.mk (span (range f))) Ideal.Quotient.mk_surjective
  exact Set.infinite_image_iff (Set.injOn_of_injective hcomap_inj) |>.mp hI_inf
