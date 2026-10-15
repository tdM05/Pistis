import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators


/-- This auxiliary lemma isolates the eventual stabilization hypothesis (condition (ii))
into the existence of a divisibility-minimal nonzero element inside any nonzero ideal. -/
lemma exists_minimal_nonzero_mem
    {R : Type*} [CommRing R] [IsDomain R]
    (h2 : ∀ a : ℕ → R, (∀ i : ℕ, a i ≠ 0 ∧ a (i + 1) ∣ a i) →
      ∃ N : ℕ, ∀ n ≥ N, ∃ u : R, IsUnit u ∧ a n = u * a N)
    {I : Ideal R} (hI : I ≠ (⊥ : Ideal R)) :
    ∃ a ∈ I, a ≠ (0 : R) ∧
      ∀ {b}, b ∈ I → b ≠ 0 → b ∣ a → Associated b a := by
  classical
  -- Step 1: Extract a first witness `a₀ ∈ I` with `a₀ ≠ 0` using the nontriviality of `I`.
  have h_nonzero : ∃ a ∈ I, a ≠ (0 : R) := by
    -- Step 1.1: Argue by contradiction that otherwise `I` would equal `⊥`.
    by_contra h
    -- Step 1.2: Convert the negated existential into a statement saying everything in `I` is zero.
    push_neg at h
    -- Step 1.3: Show the assumption forces `I = ⊥`, contradicting `hI`.
    have : I = (⊥ : Ideal R) := by
      ext x; constructor
      · intro hx
        have hx_zero : x = 0 := h x hx
        simp [hx_zero]
      · intro hx
        have hx_zero : x = 0 := by simpa [Ideal.mem_bot] using hx
        simp [hx_zero]
    exact hI this
  -- Step 2: Package nonzero elements of `I` as a subtype to manipulate divisibility chains.
  rcases h_nonzero with ⟨a₀, ha₀_mem, ha₀_ne⟩
  let S := {a : R // a ∈ I ∧ a ≠ 0}
  have base : S := ⟨a₀, ⟨ha₀_mem, ha₀_ne⟩⟩
  -- Step 3: Prove there exists a divisibility-minimal element in `S` using `h2`.
  have h_min :
      ∃ a : S, ∀ b : S, b.val ∣ a.val → Associated b.val a.val := by
    -- Step 3.1: Suppose there is no such minimal element and derive a contradiction.
    classical
    by_contra hminimal
    -- Step 3.2: From the negation, obtain a function picking a strictly smaller divisor each time.
    have hdesc :
        ∀ a : S, ∃ b : S, b.val ∣ a.val ∧ ¬ Associated b.val a.val := by
      classical
      have hnot := not_exists.mp hminimal
      intro a
      have hb := not_forall.mp (hnot a)
      rcases hb with ⟨b, hb⟩
      have hb' := Classical.not_imp.mp hb
      exact ⟨b, hb'⟩
    choose desc hdesc_spec using hdesc
    -- Step 3.3: Build the infinite divisibility chain using recursion.
    let seq : ℕ → S := fun n => Nat.rec base (fun _ prev => desc prev) n
    have hseq_succ : ∀ n, seq (n + 1) = desc (seq n) := by
      intro n; rfl
    -- Step 3.4: Verify that the sequence satisfies the hypotheses of `h2`.
    let aSeq : ℕ → R := fun n => (seq n).val
    have hSeq_cond : ∀ n, aSeq n ≠ 0 ∧ aSeq (n + 1) ∣ aSeq n := by
      intro n
      refine ⟨(seq n).property.2, ?_⟩
      simpa [aSeq, hseq_succ] using (hdesc_spec (seq n)).1
    -- Step 3.5: Apply `h2` to obtain eventual stabilization (associates).
    obtain ⟨N, hN⟩ := h2 aSeq hSeq_cond
    -- Step 3.6: Specialize stabilization at `N+1` to contradict the strict descent.
    have h_assoc_from_h2 :
        Associated (aSeq (N + 1)) (aSeq N) := by
      have hge : N ≤ N + 1 := Nat.le_of_lt (Nat.lt_succ_self _)
      obtain ⟨u, hu, hEq⟩ := hN (N + 1) hge
      obtain ⟨u', rfl⟩ := hu
      have hAssoc : Associated (aSeq N) (aSeq (N + 1)) := by
        refine ⟨u', ?_⟩
        simpa [aSeq, mul_comm] using hEq.symm
      exact Associated.symm hAssoc
    -- Step 3.7: But `desc` explicitly forbids `seq (N+1)` being associated to `seq N`.
    have h_forbid := (hdesc_spec (seq N)).2
    have h_contra : False := by
      exact h_forbid <| by simpa [aSeq, hseq_succ] using h_assoc_from_h2
    exact h_contra.elim
  -- Step 4: Extract the actual element and translate back to `R`.
  rcases h_min with ⟨aS, haS_min⟩
  refine ⟨aS.val, aS.property.1, aS.property.2, ?_⟩
  -- Step 4.1: The minimality property translates to arbitrary `b ∈ I`.
  intro b hb_mem hb_ne hb_dvd
  exact haS_min ⟨b, ⟨hb_mem, hb_ne⟩⟩ hb_dvd


/-Informal Statement

Let $R$ be an integral domain. Prove that if the following two conditions hold then $R$ is a Principal Ideal Domain: (i) any two nonzero elements $a$ and $b$ in $R$ have a greatest common divisor which can be written in the form $r a+s b$ for some $r, s \in R$, and (ii) if $a_{1}, a_{2}, a_{3}, \ldots$ are nonzero elements of $R$ such that $a_{i+1} \mid a_{i}$ for all $i$, then there is a positive integer $N$ such that $a_{n}$ is a unit times $a_{N}$ for all $n \geq N$.
-/

/-Informal Proof

Let $I \leq R$ be a nonzero ideal and let $I / \sim$ be the set of equivalence classes of elements of $I$ with regards to the relation of being associates. We can equip $I / \sim$ with a partial order with $[x] \leq[y]$ if $y \mid x$. Condition (ii) implies all chains in $I / \sim$ have an upper bound, so By Zorn's lemma $I / \sim$ contains a maximal element, i.e. $I$ contains a class of associated elements which are minimal with respect to divisibility.

Now let $a, b \in I$ be two elements such that $[a]$ and $[b]$ are minimal with respect to divisibility. By condition (i) $a$ and $b$ have a greatest common divisor $d$ which can be expressed as $d=$ $a x+b y$ for some $x, y \in R$. In particular, $d \in I$. Since $a$ and $b$ are minimal with respect to divisibility, we have that $[a]=[b]=[d]$. Therefore $I$ has at least one element $a$ that is minimal with regard to divisibility and all such elements are associate, and we have $I=\langle a\rangle$ and so $I$ is principal. We conclude $R$ is a principal ideal domain.
-/

theorem Dummit_Foote_exercise_8_2_4 {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
  (h1 : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ r s : R, gcd a b = r*a + s*b)
  (h2 : ∀ a : ℕ → R, (∀ i : ℕ, a i ≠ 0 ∧ a (i + 1) ∣ a i) →
  ∃ N : ℕ, ∀ n ≥ N, ∃ u : R, IsUnit u ∧ a n = u * a N) :
  IsPrincipalIdealRing R := by
  classical
  -- Step 1: Reduce the goal to providing, for each ideal, an explicit principal generator.
  refine ⟨?_⟩
  intro I
  -- Step 2: Split the argument into the zero ideal and the nonzero ideal cases.
  by_cases hI : I = (⊥ : Ideal R)
  · -- Step 2.1: The zero ideal is generated by `0`.
    refine ⟨0, ?_⟩
    have hspan : Ideal.span ({(0 : R)} : Set R) = (⊥ : Ideal R) :=
      Ideal.span_singleton_eq_bot.mpr rfl
    -- Step 2.1.1: Conclude by rewriting both sides to `⊥`.
    simp [hI, hspan]
  · -- Step 3: Assume `I` is nonzero and extract a divisibility-minimal element using `h2`.
    obtain ⟨a, ha_mem, ha_ne, ha_min⟩ :=
      exists_minimal_nonzero_mem h2 hI
    -- Step 3.1: Show that `I` equals the principal ideal generated by this `a`.
    refine ⟨a, ?_⟩
    refine le_antisymm ?hIle ?hspanle
    · -- Step 3.1.1: Every element of `I` lies in `(a)` by a gcd argument.
      intro b hb
      -- Step 3.1.2.1: Handle the trivial case `b = 0`.
      by_cases hb_zero : b = 0
      · simp [hb_zero]
      -- Step 3.1.2.2: Apply condition (i) to `a` and `b`.
      obtain ⟨r, s, hcomb⟩ := h1 a b ha_ne hb_zero
      -- Step 3.1.2.3: Record that the Bézout combination lies in `I`, hence so does `gcd a b`.
      have hra : r * a ∈ I := I.mul_mem_left _ ha_mem
      have hsb : s * b ∈ I := I.mul_mem_left _ hb
      have hgcd_mem : gcd a b ∈ I := by
        have : r * a + s * b ∈ I := I.add_mem hra hsb
        simpa [hcomb] using this
      -- Step 3.1.2.4: The gcd is nonzero because it divides the chosen nonzero `a`.
      have hgcd_ne : gcd a b ≠ 0 := by
        intro hzero
        rcases gcd_dvd_left a b with ⟨c, hc⟩
        have : a = 0 := by simpa [hzero] using hc
        exact ha_ne this
      -- Step 3.1.2.5: Minimality forces the gcd to be associated to `a`.
      have h_assoc : Associated (gcd a b) a :=
        ha_min hgcd_mem hgcd_ne (gcd_dvd_left a b)
      -- Step 3.1.2.6: Therefore `a` divides `b`, so `b` belongs to the ideal generated by `a`.
      have h_dvd : a ∣ b :=
        (Associated.dvd_iff_dvd_left h_assoc).mp (gcd_dvd_right a b)
      exact (Ideal.mem_span_singleton).2 h_dvd
    · -- Step 3.1.2: `(a)` is contained in `I` because `a ∈ I`.
      exact (Ideal.span_singleton_le_iff_mem (I := I)).mpr ha_mem
