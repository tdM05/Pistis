import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Show that $(p - 1)/2$ of the numbers $1, 2, \ldots, p - 1$ are quadratic residues and $(p - 1)/2$ are quadratic nonresidues $\mod p$.
-/

/-Informal Proof

To find all the quadratic residues $\bmod p$ among the integers $1,2, \ldots, p-1$, we compute the least positive residues modulo $p$ of the squares of the integers $1,2, \ldots, p-1\}$.

Since there are $p-1$ squares to consider, and since each congruence $x^2 \equiv a (\bmod p)$ has either zero or two solutions, there must be exactly $\frac{(p-1)}{2}$ quadratic residues mod $p$ among the integers $1,2, \ldots, p-1$.
The remaining
$$
(p-1)-\frac{(p-1)}{2}=\frac{(p-1)}{2}
$$
positive integers less than $p-1$ are quadratic non-residues of $\bmod p$.
-/

theorem Herstein_exercise_4_4_9 (p : ℕ) (hp : Nat.Prime p) (hodd : p % 2 = 1) :
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ∃ x : ZMod p, x^2 = q) ∧
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ¬ ∃ x : ZMod p, x^2 = q) := by
  classical
  -- Step 1: Turn the prime hypothesis into a `Fact` so `ZMod p` is a field.
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  -- Step 1.1: Since `p % 2 = 1`, ensure `p ≠ 2`.
  have hpne2 : p ≠ 2 := by
    intro h
    simp [h] at hodd
  -- Step 1.2: Collect convenient inequalities such as `2 < p`.
  have htwo_le : 2 ≤ p := Nat.succ_le_of_lt hp.one_lt
  have htwo_lt : 2 < p := lt_of_le_of_ne htwo_le (by simpa [eq_comm] using hpne2)
  have hpos : 0 < p := hp.pos
  have hpred_lt : p - 1 < p := Nat.pred_lt (Nat.ne_of_gt hpos)
  -- Step 2: Introduce the number `N = (p - 1) / 2` that should count both residues and nonresidues.
  set N : ℕ := (p - 1) / 2 with hNdef
  -- Step 2.1: Show `p = 2 * N + 1`.
  obtain ⟨k, hk⟩ := Nat.Prime.even_sub_one hp hpne2
  have htwo_mul_N : 2 * N = p - 1 := by
    have : 2 ∣ p - 1 := ⟨k, by simpa [two_mul, Nat.mul_comm] using hk⟩
    simpa [N] using (Nat.mul_div_cancel' (n := 2) (m := p - 1) this)
  have hp_eq : p = 2 * N + 1 := by
    have hcalc : (p - 1) + 1 = p := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
    calc
      p = (p - 1) + 1 := hcalc.symm
      _ = 2 * N + 1 := by simp [htwo_mul_N]
  -- Step 2.2: Define the combinatorial sets we shall work with.
  let base : Finset ℕ := (Finset.range (N + 1)).erase 0
  let residues : Finset (ZMod p) :=
    base.attach.image fun n => (n.1 : ZMod p) ^ 2
  let nonZero : Finset (ZMod p) := (Finset.univ.erase (0 : ZMod p))
  let nonres : Finset (ZMod p) := nonZero \ residues
  -- Step 3: Basic properties of numbers in `base`.
  have hbase_bounds :
      ∀ {n : ℕ}, n ∈ base → 1 ≤ n ∧ n ≤ N := by
    intro n hn
    rcases Finset.mem_erase.mp hn with ⟨hnzero, hnrange⟩
    have hlt : n < N + 1 := Finset.mem_range.mp hnrange
    have hle : n ≤ N := Nat.lt_succ_iff.mp hlt
    have hpos : 0 < n := Nat.pos_of_ne_zero hnzero
    exact ⟨Nat.succ_le_of_lt hpos, hle⟩
  have hN_lt_p : N < p := by
    have hN_le_pred : N ≤ p - 1 := Nat.div_le_self (p - 1) 2
    exact lt_of_le_of_lt hN_le_pred hpred_lt
  -- Step 3.1: Each `n ∈ base` reduces to a nonzero element of `ZMod p`.
  have hbase_cast_ne_zero :
      ∀ {n : ℕ}, n ∈ base → (n : ZMod p) ≠ 0 := by
    intro n hn
    rcases hbase_bounds hn with ⟨hn_pos, hn_le⟩
    have hn_lt : n < p := lt_of_le_of_lt hn_le hN_lt_p
    have hnot : ¬ p ∣ n := by
      intro hdiv
      have hn_pos' : 0 < n := (Nat.succ_le_iff).1 hn_pos
      have hle : p ≤ n := Nat.le_of_dvd hn_pos' hdiv
      exact (lt_irrefl _ (lt_of_le_of_lt hle hn_lt))
    exact fun hzero =>
      hnot ((ZMod.natCast_eq_zero_iff (a := n) (b := p)).1 hzero)
  -- Step 4: The squaring map on `base` is injective, giving exactly `N` residues.
  have hsq_inj :
      ∀ {a b : ℕ}, a ∈ base → b ∈ base →
        (a : ZMod p) ^ 2 = (b : ZMod p) ^ 2 → a = b := by
    intro a b ha hb hsq
    have ha_bounds := hbase_bounds ha
    have hb_bounds := hbase_bounds hb
    have hprod :
        ((a : ZMod p) + (b : ZMod p)) * ((a : ZMod p) - (b : ZMod p)) = 0 := by
      have := (sub_eq_zero.mpr hsq :
        (a : ZMod p) ^ 2 - (b : ZMod p) ^ 2 = 0)
      simpa [sq_sub_sq] using this
    have hsum_le : a + b ≤ p - 1 := by
      have : a + b ≤ N + N := add_le_add ha_bounds.2 hb_bounds.2
      have hNN : N + N = p - 1 := by simpa [two_mul, add_comm] using htwo_mul_N
      simpa [hNN] using this
    have hsum_lt : a + b < p := lt_of_le_of_lt hsum_le hpred_lt
    have hsum_ne_zero :
        ((a : ZMod p) + (b : ZMod p)) ≠ 0 := by
      intro hsumzero
      have hdiv : p ∣ a + b := by
        have : ((a + b : ℕ) : ZMod p) = 0 := by
          simpa [Nat.cast_add] using hsumzero
        exact (ZMod.natCast_eq_zero_iff (a := a + b) (b := p)).1 this
      have hpos_sum : 0 < a + b := by
        have h1 : 1 ≤ a + b := le_trans ha_bounds.1 (Nat.le_add_right _ _)
        exact (Nat.succ_le_iff).1 h1
      have hle : p ≤ a + b := Nat.le_of_dvd hpos_sum hdiv
      exact (lt_irrefl _ (lt_of_le_of_lt hle hsum_lt))
    obtain hsumzero | hdiffzero := mul_eq_zero.mp hprod
    · exact (hsum_ne_zero hsumzero).elim
    · have hcoeeq : (a : ZMod p) = (b : ZMod p) := sub_eq_zero.mp hdiffzero
      have hmodeq : a ≡ b [MOD p] :=
        (ZMod.natCast_eq_natCast_iff (a := a) (b := b) (c := p)).1 hcoeeq
      have ha_lt : a < p := lt_of_le_of_lt ha_bounds.2 hN_lt_p
      have hb_lt : b < p := lt_of_le_of_lt hb_bounds.2 hN_lt_p
      exact Nat.ModEq.eq_of_lt_of_lt hmodeq ha_lt hb_lt
  have hbase_card : base.card = N := by
    have hzero_mem : (0 : ℕ) ∈ Finset.range (N + 1) :=
      Finset.mem_range.mpr (Nat.succ_pos _)
    simp [base, Nat.add_comm]
  have hres_card : residues.card = N := by
    have hinj :
        Set.InjOn
          (fun n : {x // x ∈ base} => (n.1 : ZMod p) ^ 2)
          (↑(base.attach) : Set _) := by
      intro a _ b _ hsq
      apply Subtype.ext
      exact hsq_inj a.property b.property hsq
    have hcard :=
      (Finset.card_image_iff
        (s := base.attach)
        (f := fun n : {x // x ∈ base} => (n.1 : ZMod p) ^ 2)).mpr hinj
    calc
      residues.card = base.attach.card := by simpa [residues] using hcard
      _ = base.card := by simp
      _ = N := hbase_card
  -- Step 5: Describe which `ZMod p` elements lie in `residues`.
  have hzero_not_mem_residues : (0 : ZMod p) ∉ residues := by
    intro h
    rcases Finset.mem_image.mp h with ⟨n, hn, hsq⟩
    have hzero : (n.1 : ZMod p) = 0 := by
      have := (by simpa [pow_two] using hsq :
        (n.1 : ZMod p) * (n.1 : ZMod p) = 0)
      rcases mul_eq_zero.mp this with hzero | hzero <;> exact hzero
    exact (hbase_cast_ne_zero n.property) hzero
  have hres_subset_nonZero : residues ⊆ nonZero := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨n, hn, rfl⟩
    have : (n.1 : ZMod p) ≠ 0 := hbase_cast_ne_zero n.property
    have hpow : (n.1 : ZMod p) ^ 2 ≠ 0 := pow_ne_zero _ this
    simp [nonZero, hpow]
  have hres_property :
      ∀ {q : ZMod p}, q ∈ residues → ∃ x : ZMod p, x ^ 2 = q := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨n, hn, rfl⟩
    exact ⟨(n.1 : ZMod p), rfl⟩
  -- Step 5.1: Show that every nonzero square actually lands inside `residues`.
  have hsquare_mem :
      ∀ {q : ZMod p}, q ≠ 0 → (∃ x : ZMod p, x ^ 2 = q) → q ∈ residues := by
    intro q hq hsq
    rcases hsq with ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      intro hxzero
      have : 0 = q := by simpa [hxzero] using hx
      exact hq this.symm
    set a : ℕ := x.val with ha_def
    have ha_lt : a < p := ZMod.val_lt x
    have hxval : ((a : ZMod p)) = x := ZMod.natCast_zmod_val x
    have ha_ne : a ≠ 0 := by
      intro ha0
      have hxzero : x = 0 := by
        simpa [ha0] using hxval.symm
      exact hx0 hxzero
    have hx_square : (a : ZMod p) ^ 2 = q := by
      simpa [hxval] using hx
    by_cases hcase : a ≤ N
    · have ha_mem : a ∈ base := by
        refine Finset.mem_erase.mpr ?_
        refine ⟨ha_ne, ?_⟩
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hcase)
      refine Finset.mem_image.mpr ?_
      refine ⟨⟨a, ha_mem⟩, ?_⟩
      refine ⟨by simp, ?_⟩
      simp [hx_square]
    · -- Use the symmetric representative `p - a`.
      have ha_ge : N + 1 ≤ a := Nat.succ_le_of_lt (lt_of_not_ge hcase)
      set b : ℕ := p - a
      have hb_pos : 0 < b := Nat.sub_pos_of_lt ha_lt
      have hb_ne : b ≠ 0 := ne_of_gt hb_pos
      have hb_le : b ≤ N := by
        have hsub := Nat.sub_le_sub_left ha_ge p
        have hrewrite : p = N + (N + 1) := by
          simp [hp_eq, two_mul, Nat.add_comm, Nat.add_left_comm]
        have hcalc : p - (N + 1) = N := by
          simp [hrewrite]
        omega
      have hb_mem : b ∈ base := by
        refine Finset.mem_erase.mpr ?_
        refine ⟨hb_ne, ?_⟩
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hb_le)
      have hb_cast : ((b : ℕ) : ZMod p) = - (a : ZMod p) := by
        have hle : a ≤ p := Nat.le_of_lt ha_lt
        simp [b, Nat.cast_sub hle]
      have hqb : (b : ZMod p) ^ 2 = q := by
        simp [hb_cast, hx_square]
      refine Finset.mem_image.mpr ?_
      refine ⟨⟨b, hb_mem⟩, ?_⟩
      refine ⟨by simp, ?_⟩
      simp [hqb]
  -- Step 6: Control the complement (nonresidues).
  have hnonzero_card : nonZero.card = p - 1 := by
    have hmem : (0 : ZMod p) ∈ (Finset.univ : Finset (ZMod p)) := Finset.mem_univ _
    simp [nonZero, ZMod.card, Finset.card_univ]
  have hnonres_card :
      nonres.card = N := by
    have hcard :
        nonres.card = nonZero.card - (residues ∩ nonZero).card := by
      simpa [nonres] using
        (Finset.card_sdiff (s := residues) (t := nonZero))
    have hsub_eq :
        (p - 1) - N = N := by
      have hNN : N + N = p - 1 := by simpa [two_mul, add_comm] using htwo_mul_N
      simpa [hNN] using Nat.add_sub_cancel N N
    have hinter : residues ∩ nonZero = residues :=
      Finset.inter_eq_left.mpr hres_subset_nonZero
    simp [nonres, hcard, hinter, hnonzero_card, hres_card, hsub_eq]
  have hnonres_subset_nonZero : nonres ⊆ nonZero := by
    simp [nonres]
  have hzero_not_mem_nonZero : (0 : ZMod p) ∉ nonZero := by
    simp [nonZero]
  have hzero_not_mem_nonres : (0 : ZMod p) ∉ nonres := fun h =>
    hzero_not_mem_nonZero (hnonres_subset_nonZero h)
  have hnonres_property :
      ∀ {q : ZMod p}, q ∈ nonres → ¬ ∃ x : ZMod p, x ^ 2 = q := by
    intro q hq hsq
    rcases Finset.mem_sdiff.mp hq with ⟨hq_nonzero, hq_not_res⟩
    have hq_ne_zero : q ≠ 0 := by simpa [nonZero] using hq_nonzero
    have hmem := hsquare_mem hq_ne_zero hsq
    exact hq_not_res hmem
  -- Step 7: Package everything into the required pair of sets.
  refine ⟨?_resPart, ?_nonResPart⟩
  · -- Step 7.1: Quadratic residues form a set of size `(p - 1) / 2` without zero.
    refine ⟨residues, hzero_not_mem_residues, ?_, ?_⟩
    · simpa [N] using hres_card
    · intro q hq
      exact hres_property hq
  · -- Step 7.2: Their complement inside the nonzeros gives the quadratic nonresidues.
    refine ⟨nonres, hzero_not_mem_nonres, ?_, ?_⟩
    · simpa [N] using hnonres_card
    · intro q hq
      exact hnonres_property hq
