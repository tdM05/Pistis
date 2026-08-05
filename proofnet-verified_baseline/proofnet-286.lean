import Mathlib

open Real
open scoped BigOperators Finset



/-Informal Statement

Prove that $1^{k}+2^{k}+\cdots+(p-1)^{k} \equiv 0(p)$ if $p-1 \nmid k$ and $-1(p)$ if $p-1 \mid k$.
-/

/-Informal Proof

Let $S_k = 1^k+2^k+\cdots+(p-1)^k$.

Let $g$ a primitive root modulo $p$ : $\overline{g}$ a generator of $\mathbb{F}_p^*$.

As $(\overline{1},\overline{g},\overline{g}^{2}, \ldots, \overline{g}^{p-2}) $ is a permutation of $ (\overline{1},\overline{2}, \ldots,\overline{p-1})$,
\begin{align*}
\overline{S_k} &= \overline{1}^k + \overline{2}^k+\cdots+ \overline{p-1}^k\\
&= \sum_{i=0}^{p-2} \overline{g}^{ki} =
\left\{
\begin{array}{ccc}
\overline{ p-1} = -\overline{1} &  \mathrm{if} &  p-1 \mid k  \\
 \frac{ \overline{g}^{(p-1)k} -1}{ \overline{g}^k -1} = \overline{0}&  \mathrm{if}  &   p-1 \nmid k
\end{array}
\right.
\end{align*}
since $p-1 \mid k \iff \overline{g}^k = \overline{1}$.

Conclusion :
\begin{align*}
1^k+2^k+\cdots+(p-1)^k&\equiv 0 \pmod p\ \mathrm{if} \ p-1 \nmid k\\
1^k+2^k+\cdots+(p-1)^k&\equiv -1 \pmod p\ \mathrm{if} \ p-1 \mid k\\
\end{align*}
-/

theorem Ireland_Rosen_exercise_4_11 {p : ℕ} (hp : p.Prime) (k s: ℕ)
  (hs : s = ∑ n : Fin (p-1), (n + 1 : ℕ) ^ k) :
  ((¬ p - 1 ∣ k) → s ≡ 0 [MOD p]) ∧ (p - 1 ∣ k → s ≡ -1 [ZMOD p]) := by
  classical
  -- Step 1: Basic arithmetic facts about the prime `p`.
  -- Step 1.1: Record that `p ≥ 2`, hence `1 < p` and `p ≠ 0`.
  have hp_two_le : 2 ≤ p := hp.two_le
  have hp_one_lt : 1 < p := hp.one_lt
  have hp_ne_zero : p ≠ 0 := hp.ne_zero
  -- Step 1.2: Package `p.Prime` as a `Fact` instance for the `ZMod p` lemmas.
  haveI : Fact p.Prime := ⟨hp⟩
  -- Step 1.3: It will be convenient to know that `p - 1 < p`.
  have hp_pred_lt : p - 1 < p := by
    have h := Nat.lt_succ_self (p - 1)
    -- `Nat.lt_succ_self (p - 1)` states `p - 1 < (p - 1).succ`;
    -- rewrite `(p - 1).succ` as `p`.
    simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hp.one_le] using h

  -- Step 2: Identify the sum `s` inside `ZMod p`.
  -- We will repeatedly use the fact that casting a sum and a power
  -- from `ℕ` to `ZMod p` commutes with both operations.
  -- Step 2.1: Express the cast of `s` in terms of the original finite sum.
  have h_s_zmod :
      (s : ZMod p) =
        ∑ n : Fin (p - 1), ((n + 1 : ℕ) : ZMod p) ^ k := by
    -- Step 2.1.1: Replace `s` by the defining sum and push the cast through.
    -- Each term `(n + 1 : ℕ) ^ k` becomes `((n + 1 : ZMod p)) ^ k`.
    simp [hs, Nat.cast_sum, Nat.cast_pow]

  -- Step 3: Relate the `Fin (p-1)`-indexed sum to a sum over the nonzero elements of `ZMod p`.
  -- We build an embedding `ψ : Fin (p - 1) ↪ ZMod p` sending `n ↦ (n+1 : ZMod p)`,
  -- and show that its image is precisely the set of nonzero elements.
  -- This allows us to reindex the sum.
  -- Step 3.1: Define the embedding `ψ`.
  let ψ : Fin (p - 1) ↪ ZMod p :=
    { toFun := fun n => ((n : ℕ) + 1 : ZMod p)
      , inj' :=
        by
          -- Step 3.1.1: Prove injectivity of `ψ`.
          -- Suppose `(n + 1 : ZMod p) = (m + 1 : ZMod p)`; cancel the `+1`,
          -- and then use boundedness to conclude `n = m`.
          intro n m h_eq
          -- Step 3.1.1.1: Cancel the `+ 1` on both sides of the equality.
          have h_eq' :
              ((n : ZMod p)) = (m : ZMod p) := by
            -- Subtract `1` on both sides.
            have := congrArg (fun x : ZMod p => x - (1 : ZMod p)) h_eq
            -- Simplify both sides.
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
          -- Step 3.1.1.2: Rewrite in terms of natural-number casts.
          have h_eq_nat_cast :
              ((n : ℕ) : ZMod p) = ((m : ℕ) : ZMod p) := by
            simpa using h_eq'
          -- Step 3.1.1.3: View this as a congruence modulo `p`.
          have h_modeq :
              (n : ℕ) ≡ (m : ℕ) [MOD p] :=
            (ZMod.natCast_eq_natCast_iff (a := (n : ℕ)) (b := (m : ℕ)) (c := p)).1
              h_eq_nat_cast
          -- Step 3.1.1.4: Bound both indices by `p` and upgrade congruence to equality.
          have hn_lt : (n : ℕ) < p := by
            have hn_lt_pred : (n : ℕ) < p - 1 := n.is_lt
            have hn_le_pred : (n : ℕ) ≤ p - 1 := le_of_lt hn_lt_pred
            exact lt_of_le_of_lt hn_le_pred hp_pred_lt
          have hm_lt : (m : ℕ) < p := by
            have hm_lt_pred : (m : ℕ) < p - 1 := m.is_lt
            have hm_le_pred : (m : ℕ) ≤ p - 1 := le_of_lt hm_lt_pred
            exact lt_of_le_of_lt hm_le_pred hp_pred_lt
          -- Step 3.1.1.5: Use the definition of `Nat.ModEq` and the bounds to deduce `n = m`.
          have h_eq_nat : (n : ℕ) = (m : ℕ) := by
            -- Step 3.1.1.5.1: Unfold the definition of `Nat.ModEq` to get an equality of remainders.
            -- At this point `h_modeq : (n : ℕ) ≡ (m : ℕ) [MOD p]`.
            -- By unfolding, we obtain `(n : ℕ) % p = (m : ℕ) % p`.
            have h_mod : (n : ℕ) % p = (m : ℕ) % p := by
              -- `Nat.ModEq` is definitionally `(· % p = · % p)`.
              simpa [Nat.ModEq] using h_modeq
            -- Step 3.1.1.5.2: Since both `n` and `m` are strictly less than `p`,
            -- their remainders modulo `p` are themselves.
            have hn_mod : (n : ℕ) % p = (n : ℕ) :=
              Nat.mod_eq_of_lt hn_lt
            have hm_mod : (m : ℕ) % p = (m : ℕ) :=
              Nat.mod_eq_of_lt hm_lt
            -- Step 3.1.1.5.3: Chain these equalities to obtain `(n : ℕ) = (m : ℕ)`.
            calc
              (n : ℕ)
                  = (n : ℕ) % p := by simp [hn_mod]
              _ = (m : ℕ) % p := h_mod
              _ = (m : ℕ) := hm_mod
          -- Step 3.1.1.6: Conclude the equality of `Fin` elements from equality of their values.
          exact Fin.ext h_eq_nat }

  -- Step 3.2: Show that the image of `ψ` is exactly the set of nonzero elements of `ZMod p`.
  have h_image_nonzero :
      (Finset.univ.map ψ) =
        (Finset.univ : Finset (ZMod p)).erase 0 := by
    -- Step 3.2.1: First show that every element in the image of `ψ` is nonzero.
    have h_subset :
        (Finset.univ.map ψ) ⊆ (Finset.univ : Finset (ZMod p)).erase 0 := by
      intro x hx
      rcases Finset.mem_map.1 hx with ⟨n, -, rfl⟩
      -- Now `x = (n + 1 : ZMod p)`; this element cannot be zero.
      have hx_ne_zero : ((n : ℕ) + 1 : ZMod p) ≠ 0 := by
        intro h_zero
        -- From `(n+1 : ZMod p) = 0`, we get `p ∣ n+1`.
        have h_dvd : (p : ℕ) ∣ (n : ℕ) + 1 := by
          -- Step 3.2.1.1: Rewrite the hypothesis so that it matches the lemma
          -- `ZMod.natCast_eq_zero_iff`.
          have h_zero' : ((↑n + 1 : ℕ) : ZMod p) = 0 := by
            simpa using h_zero
          -- Step 3.2.1.2: Apply `ZMod.natCast_eq_zero_iff` to deduce the divisibility.
          exact
            (ZMod.natCast_eq_zero_iff (a := (↑n + 1 : ℕ)) (b := p)).1 h_zero'
        -- But `n+1 ≤ p-1`, so `p ≤ n+1 ≤ p-1`, impossible.
        have hn_pos : 0 < (n : ℕ) + 1 := Nat.succ_pos _
        have hp_le : p ≤ (n : ℕ) + 1 :=
          Nat.le_of_dvd hn_pos h_dvd
        have hn_le : (n : ℕ) + 1 ≤ p - 1 := by
          have hn_lt_pred : (n : ℕ) < p - 1 := n.is_lt
          exact Nat.succ_le_of_lt hn_lt_pred
        have : p ≤ p - 1 := le_trans hp_le hn_le
        have : p < p := lt_of_le_of_lt this hp_pred_lt
        exact lt_irrefl _ this
      exact Finset.mem_erase.mpr ⟨hx_ne_zero, Finset.mem_univ _⟩
    -- Step 3.2.2: Compute the cardinalities of both sides.
    have h_card_map :
        (Finset.univ.map ψ).card = p - 1 := by
      -- Mapping along an embedding preserves cardinality.
      have h1 :
          (Finset.univ.map ψ).card =
            (Finset.univ : Finset (Fin (p - 1))).card := by
        simp [Finset.card_map]
      have h2 :
          (Finset.univ : Finset (Fin (p - 1))).card =
            Fintype.card (Fin (p - 1)) := by
        simp [Finset.card_univ]
      have h3 : Fintype.card (Fin (p - 1)) = p - 1 :=
        Fintype.card_fin (p - 1)
      linarith [h1, h2, h3]
    have h_card_erase :
        ((Finset.univ : Finset (ZMod p)).erase 0).card = p - 1 := by
      -- The nonzero elements are all but one of the `p` elements of `ZMod p`.
      have h0_mem :
          (0 : ZMod p) ∈ (Finset.univ : Finset (ZMod p)) :=
        Finset.mem_univ _
      have h_card_erase' :
          ((Finset.univ : Finset (ZMod p)).erase 0).card =
            (Finset.univ : Finset (ZMod p)).card - 1 :=
        Finset.card_erase_of_mem (s := (Finset.univ : Finset (ZMod p)))
          (a := (0 : ZMod p)) h0_mem
      have h_card_univ :
          (Finset.univ : Finset (ZMod p)).card = p := by
        simp [ZMod.card p, Finset.card_univ]
      omega
    -- Step 3.2.3: Use subset and equal cardinalities to deduce set equality.
    exact
      (Finset.eq_iff_card_le_of_subset h_subset).mp <| by
        -- We need `#(univ.erase 0) ≤ #(univ.map ψ)`, but both are `p - 1`.
        have h_eq_card :
            ((Finset.univ : Finset (ZMod p)).erase 0).card =
              (Finset.univ.map ψ).card := by
          simp [h_card_map, h_card_erase]
        exact h_eq_card.le

  -- Step 3.3: Rewrite the sum over `Fin (p-1)` through `ψ` as a sum over the nonzero elements.
  have h_sum_nonzero :
      (∑ n : Fin (p - 1), ((n + 1 : ℕ) : ZMod p) ^ k) =
        ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, x ^ k := by
    -- Use `Finset.univ.sum_map` to reindex the sum along `ψ`
    -- and then identify the image with `univ.erase 0`.
    -- The lemma `Finset.sum_map` gives the equality in the opposite direction;
    -- we flip it with `.symm` to match our desired orientation.
    have h := (Finset.univ.sum_map ψ fun x : ZMod p => x ^ k)
    simpa [ψ, h_image_nonzero] using h.symm

  -- Step 3.4: Combine the previous equalities to identify `(s : ZMod p)` as a sum
  -- over the nonzero elements of `ZMod p`.
  have h_s_nonzero :
      (s : ZMod p) =
        ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, x ^ k := by
    -- Chain `h_s_zmod` with `h_sum_nonzero`.
    calc
      (s : ZMod p)
          = ∑ n : Fin (p - 1), ((n + 1 : ℕ) : ZMod p) ^ k := h_s_zmod
      _ = ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, x ^ k := h_sum_nonzero

  -- Step 4: Relate the sum over nonzero elements to the sum over units `(ZMod p)ˣ`.
  -- This follows the pattern used in `FiniteField.sum_pow_lt_card_sub_one`.
  -- Step 4.1: Define the embedding from units to the underlying field.
  let φ_units : (ZMod p)ˣ ↪ ZMod p :=
    ⟨fun x => (x : ZMod p), Units.val_injective⟩

  -- Step 4.2: The image of `φ_units` is exactly the set of nonzero elements.
  have h_units_nonzero :
      Finset.univ.map φ_units =
        (Finset.univ : Finset (ZMod p)).erase 0 := by
    -- This is exactly the same argument as in `FiniteField.sum_pow_lt_card_sub_one`.
    -- Any unit is nonzero, and conversely any nonzero element of a field is a unit.
    ext x
    constructor
    · intro hx
      rcases Finset.mem_map.1 hx with ⟨u, -, rfl⟩
      have hu_ne : (u : ZMod p) ≠ 0 := by
        exact isUnit_iff_ne_zero.mp u.isUnit
      exact Finset.mem_erase.mpr ⟨hu_ne, Finset.mem_univ _⟩
    · intro hx
      rcases Finset.mem_erase.1 hx with ⟨hx_ne_zero, -⟩
      have hx_unit : IsUnit x := isUnit_iff_ne_zero.mpr hx_ne_zero
      rcases hx_unit with ⟨u, rfl⟩
      exact Finset.mem_map.mpr ⟨u, Finset.mem_univ _, rfl⟩

  -- Step 4.3: Reindex the sum over `(ZMod p)ˣ` along `φ_units`.
  have h_sum_units :
      ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, x ^ k =
        ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ k := by
    -- This is exactly the reindexing used in `FiniteField.sum_pow_lt_card_sub_one`.
    have := (Finset.univ.sum_map φ_units fun x : ZMod p => x ^ k)
    simpa [φ_units, h_units_nonzero] using this

  -- Step 4.4: Combine all the equalities: `(s : ZMod p)` is the sum over units.
  have h_s_units :
      (s : ZMod p) =
        ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ k := by
    calc
      (s : ZMod p)
          = ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, x ^ k := h_s_nonzero
      _ = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ k := h_sum_units

  -- Step 5: Evaluate the sum over units using `FiniteField.sum_pow_units`
  -- specialized to `K := ZMod p`, whose cardinality is `p`.
  -- Step 5.1: Identify the cardinality of `ZMod p` and its unit group.
  have h_card : Fintype.card (ZMod p) = p := ZMod.card p
  -- Step 5.2: Apply `sum_pow_units` with `K = ZMod p`.
  have h_sum_pow_units :
      (∑ u : (ZMod p)ˣ, (u : ZMod p) ^ k) =
        (if p - 1 ∣ k then (-1 : ZMod p) else 0) := by
    have := (FiniteField.sum_pow_units (K := ZMod p) k)
    simpa [h_card] using this

  -- Step 5.3: Substitute the evaluation back into the expression for `(s : ZMod p)`.
  have h_s_eval :
      (s : ZMod p) =
        if p - 1 ∣ k then (-1 : ZMod p) else 0 := by
    simp [h_s_units, h_sum_pow_units]

  -- Step 6: Prove each of the two desired congruences by translating equalities in `ZMod p`
  -- back into `Nat.ModEq` and `Int.ModEq`.

  -- Step 6.1: First branch — when `p - 1` does *not* divide `k`, the sum is `0` in `ZMod p`,
  -- so `s ≡ 0 [MOD p]`.
  have h_case_not_dvd :
      (¬ p - 1 ∣ k) → s ≡ 0 [MOD p] := by
    intro hk
    -- Step 6.1.1: Use `h_s_eval` to see that `(s : ZMod p) = 0`.
    have h_s_zero : (s : ZMod p) = 0 := by
      have : (if p - 1 ∣ k then (-1 : ZMod p) else 0) = 0 := by
        simp [hk]
      simp [h_s_eval, this]
    -- Step 6.1.2: Translate the equality `(s : ZMod p) = 0` back into `Nat.ModEq`.
    have h_s_zero' :
        ((s : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by
      -- This simply coerces `0` to `(0 : ℕ)` inside `ZMod p`.
      simpa using h_s_zero
    have h_modeq :
        s ≡ 0 [MOD p] :=
      (ZMod.natCast_eq_natCast_iff (a := s) (b := 0) (c := p)).1 h_s_zero'
    exact h_modeq

  -- Step 6.2: Second branch — when `p - 1 ∣ k`, the sum is `-1` in `ZMod p`.
  -- We must show `s ≡ -1 [ZMOD p]`.
  have h_case_dvd :
      (p - 1 ∣ k) → s ≡ -1 [ZMOD p] := by
    intro hk
    -- Step 6.2.1: Under the divisibility hypothesis, `(s : ZMod p) = -1`.
    have h_s_neg_one : (s : ZMod p) = (-1 : ZMod p) := by
      have : (if p - 1 ∣ k then (-1 : ZMod p) else 0) = (-1 : ZMod p) := by
        simp [hk]
      simp [h_s_eval, this]
    -- Step 6.2.2: Use the equivalence between equality in `ZMod p` and integer congruence.
    have h_int_modeq :
        (s : ℤ) ≡ -1 [ZMOD p] := by
      have h_cast_eq :
          ((s : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p) := by
        simpa using h_s_neg_one
      exact
        (ZMod.intCast_eq_intCast_iff (a := (s : ℤ)) (b := (-1 : ℤ)) p).1 h_cast_eq
    exact h_int_modeq

  -- Step 7: Package the two branches into the requested conjunction.
  exact ⟨h_case_not_dvd, h_case_dvd⟩
