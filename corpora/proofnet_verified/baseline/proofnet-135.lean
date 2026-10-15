import Mathlib

open Filter Real Function
open scoped Topology


/--
Step 1: show that an injective function `f : ℕ → ℕ` eventually exceeds any prescribed bound.
Step 1.1: establish the auxiliary lemma by induction on the bound `N`.
-/
private lemma eventually_ge_of_injective (f : ℕ → ℕ) (hf : Injective f) :
    ∀ N : ℕ, ∃ M : ℕ, ∀ ⦃n : ℕ⦄, M ≤ n → N ≤ f n := by
  classical
  -- Step 1.2: perform induction on `N`.
  refine Nat.rec ?base ?step
  · -- Step 1.2.1: when `N = 0`, every value of `f` is non-negative, so `M = 0` works.
    exact ⟨0, fun {_} _ => Nat.zero_le _⟩
  · -- Step 1.2.2: assume the claim for `N` and prove it for `N + 1`.
    intro N hN
    obtain ⟨M, hM⟩ := hN
    -- Step 1.2.3: split on whether some index maps to `N`.
    by_cases hNval : ∃ n, f n = N
    · -- Step 1.2.3.1: if such `n` exists, call it `nN` and avoid it by going past `nN + 1`.
      obtain ⟨nN, hnN⟩ := hNval
      refine ⟨max M (nN + 1), ?_⟩
      intro n hn
      -- Step 1.2.3.1.1: from `n ≥ max M (nN + 1)` deduce both `n ≥ M` and `n ≥ nN + 1`.
      have hgeM : M ≤ n := le_of_max_le_left hn
      have hgeSucc : nN + 1 ≤ n := le_of_max_le_right hn
      -- Step 1.2.3.1.2: values beyond `M` are at least `N` by the inductive hypothesis.
      have hNle : N ≤ f n := hM hgeM
      -- Step 1.2.3.1.3: show `f n` cannot equal `N`, otherwise injectivity contradicts `n ≥ nN + 1`.
      have hneq : f n ≠ N := by
        intro hfn
        have hSame : f n = f nN := by simp [hfn, hnN]
        have hEqIdx : n = nN := hf hSame
        have : (nN + 1) ≤ nN := by simp [hEqIdx] at hgeSucc
        exact (lt_irrefl _ (lt_of_lt_of_le (Nat.lt_succ_self _) this))
      -- Step 1.2.3.1.4: strict inequality gives the required bound `N + 1 ≤ f n`.
      have hlt : N < f n := lt_of_le_of_ne hNle (Ne.symm hneq)
      exact Nat.succ_le_of_lt hlt
    · -- Step 1.2.3.2: if no index maps to `N`, reuse the old `M` because equality never occurs.
      refine ⟨M, ?_⟩
      intro n hn
      have hNle : N ≤ f n := hM hn
      have hneq : N ≠ f n := by
        intro hEq
        exact hNval ⟨n, by simp [hEq]⟩
      have hlt : N < f n := lt_of_le_of_ne hNle hneq
      exact Nat.succ_le_of_lt hlt


/-Informal Statement

Let $(p_n)$ be a sequence and $f:\mathbb{N}\to\mathbb{N}$. The sequence $(q_k)_{k\in\mathbb{N}}$ with $q_k=p_{f(k)}$ is called a rearrangement of $(p_n)$. Show that if $f$ is an injection, the limit of a sequence is unaffected by rearrangement.
-/

/-Informal Proof

Let $\varepsilon>0$. Since $p_n \rightarrow L$, we have that, for all $n$ except $n \leq N$, $d\left(p_n, L\right)<\epsilon$. Let $S=\{n \mid f(n) \leq N\}$, let $n_0$ be the largest $n \in S$, we know there is such a largest $n$ because $f(n)$ is injective. Now we have that $\forall n>n_0 f(n)>N$ which implies that $p_{f(n)} \rightarrow L$, as required.
-/

theorem Pugh_exercise_2_12a {α : Type*} [TopologicalSpace α]
  (f : ℕ → ℕ) (p : ℕ → α) (a : α)
  (hf : Injective f) (hp : Tendsto p atTop (𝓝 a)) :
  Tendsto (λ n => p (f n)) atTop (𝓝 a) := by
  classical
  -- Step 2: convert injectivity into the fact that `f` eventually dominates every natural number.
  have hcofinal : ∀ N : ℕ, ∀ᶠ n : ℕ in atTop, N ≤ f n := by
    -- Step 2.1: use the auxiliary lemma and the characterization of `eventually` on `atTop`.
    intro N
    obtain ⟨M, hM⟩ := eventually_ge_of_injective f hf N
    exact Filter.eventually_atTop.2 ⟨M, hM⟩
  -- Step 3: reinterpret `hcofinal` as the statement that `f` tends to `+∞` in `atTop`.
  have hf_tendsto : Tendsto f atTop atTop := by
    -- Step 3.1: apply `Filter.tendsto_atTop.2` with the event described in Step 2.
    refine Filter.tendsto_atTop.2 ?_
    intro N
    simpa using hcofinal N
  -- Step 4: compose the original convergence of `p` with the cofinal map `f`.
  -- Step 4.1: `Tendsto.comp` closes the argument since `(p ∘ f)` inherits the limit.
  simpa using hp.comp hf_tendsto
