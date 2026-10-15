import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $G$ be a finite group which possesses an automorphism $\sigma$ such that $\sigma(g)=g$ if and only if $g=1$. If $\sigma^{2}$ is the identity map from $G$ to $G$, prove that $G$ is abelian.
-/

/-Informal Proof

Solution: We define a mapping $f: G \rightarrow G$ by $f(x)=x^{-1} \sigma(x)$.
Claim: $f$ is injective.
Proof of claim: Suppose $f(x)=f(y)$. Then $y^{-1} \sigma(y)=x^{-1} \sigma(x)$, so that $x y^{-1}=\sigma(x) \sigma\left(y^{-1}\right)$, and $x y^{-1}=\sigma\left(x y^{-1}\right)$. Then we have $x y^{-1}=1$, hence $x=y$. So $f$ is injective.

Since $G$ is finite and $f$ is injective, $f$ is also surjective. Then every $z \in G$ is of the form $x^{-1} \sigma(x)$ for some $x$. Now let $z \in G$ with $z=x^{-1} \sigma(x)$. We have
$$
\sigma(z)=\sigma\left(x^{-1} \sigma(x)\right)=\sigma(x)^{-1} x=\left(x^{-1} \sigma(x)\right)^{-1}=z^{-1} .
$$
Thus $\sigma$ is in fact the inversion mapping, and we assumed that $\sigma$ is a homomorphism. By a previous example, then, $G$ is abelian.
-/

theorem Dummit_Foote_exercise_1_6_23 {G : Type*}
  [Group G] (σ : MulAut G) (hs : ∀ g : G, σ g = g ↔ g = 1)
  (hs2 : ∀ g : G, σ (σ g) = g) :
  ∀ x y : G, x*y = y*x := by
  sorry

/-
The informal argument silently uses that `G` is finite in order to deduce that the map
`g ↦ g⁻¹ * σ g` is bijective.  Without the finiteness hypothesis, `σ` can still be a
fixed-point-free involution while the group remains non-abelian.  The following material
builds a concrete counterexample and a corrected statement.
-/

namespace FreeGroup

open Function

variable {α β : Type*}

lemma IsReduced.map_of_injective {L : List (α × Bool)} {f : α → β}
    (h : IsReduced L) (hf : Injective f) :
    IsReduced (L.map fun x => (f x.1, x.2)) := by
  -- Step 1: induct on the structure of the word `L`.
  induction L with
  | nil =>
      -- Step 1.1: the empty word stays reduced after any map.
      exact (IsReduced.nil (α := β))
  | cons a L ih =>
      -- Step 1.2: split on the tail to isolate the base case of a singleton word.
      cases L with
      | nil =>
          -- Step 1.2.1: single letters remain reduced under any map.
          exact (IsReduced.singleton (a := (f a.1, a.2)))
      | cons b L =>
          -- Step 1.2.2: use `IsReduced.cons_cons` to break the hypothesis into two pieces.
          have hcons := (isReduced_cons_cons (a := a) (b := b) (L := L)).1 h
          -- Step 2: the first piece provides the “no cancellation” constraint after mapping.
          have hhead :
              (f a.1 = f b.1 → a.2 = b.2) := by
            -- Step 2.1: injectivity transports equalities of images back to the sources.
            intro hfb
            exact hcons.1 (hf hfb)
          -- Step 3: recursively treat the tail.
          have htail := ih hcons.2
          -- Step 4: rebuild the chain condition after mapping.
          exact (isReduced_cons_cons (a := (f a.1, a.2)) (b := (f b.1, b.2))
            (L := _)).2 ⟨hhead, htail⟩

lemma toWord_map_of_injective [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Injective f)
    (x : FreeGroup α) :
    (FreeGroup.map f x).toWord = x.toWord.map fun y => (f y.1, y.2) := by
  -- Step 1: replace `x` by the canonical reduced word provided by `toWord`.
  have hx : x = FreeGroup.mk x.toWord := (mk_toWord (x := x)).symm
  -- Step 2: evaluate `toWord` of the mapped element via `map.mk`.
  have hmk :
      FreeGroup.map f (FreeGroup.mk x.toWord) =
        FreeGroup.mk (x.toWord.map fun y => (f y.1, y.2)) :=
    -- Step 2.1: apply the dedicated lemma for quotients.
    FreeGroup.map.mk (f := f) (L := x.toWord)
  have hmap :
      (FreeGroup.map f (FreeGroup.mk x.toWord)).toWord =
        reduce (x.toWord.map fun y => (f y.1, y.2)) := by
    -- Step 2.2: translate the equality under `toWord`.
    simp [toWord_mk]
  have hxmap :
      FreeGroup.map f x = FreeGroup.map f (FreeGroup.mk x.toWord) :=
    congrArg (FreeGroup.map f) hx
  have hxmap_toWord :
      (FreeGroup.map f x).toWord =
        (FreeGroup.map f (FreeGroup.mk x.toWord)).toWord :=
    congrArg FreeGroup.toWord hxmap
  -- Step 3: the mapped word is still reduced thanks to `hf`.
  have hReduced :
      IsReduced (x.toWord.map fun y => (f y.1, y.2)) :=
    (IsReduced.map_of_injective (α := α) (β := β) (L := x.toWord)
      (f := f) (hf := hf) (isReduced_toWord (x := x)))
  -- Step 4: finish by rewriting `x` and simplifying with the reduction lemma.
  calc
    (FreeGroup.map f x).toWord =
        (FreeGroup.map f (FreeGroup.mk x.toWord)).toWord := hxmap_toWord
    _ = reduce (x.toWord.map fun y => (f y.1, y.2)) := hmap
    _ = _ := hReduced.reduce_eq

end FreeGroup

namespace Proofnet220

open FreeGroup

private def swapEquiv : Sum Unit Unit ≃ Sum Unit Unit := Equiv.sumComm _ _

private abbrev CounterexampleGroup : Type := FreeGroup (Sum Unit Unit)

private def swapAutCounter : MulAut CounterexampleGroup :=
  FreeGroup.freeGroupCongr swapEquiv

private def swapLetter (p : Sum Unit Unit × Bool) : Sum Unit Unit × Bool :=
  (swapEquiv p.1, p.2)

lemma swapEquiv_ne_self (a : Sum Unit Unit) : swapEquiv a ≠ a := by
  -- Step 1: inspect both constructors of the sum type.
  cases a with
  | inl _ => simp [swapEquiv]
  | inr _ => simp [swapEquiv]

lemma swapEquiv_comp_self (a : Sum Unit Unit) : swapEquiv (swapEquiv a) = a := by
  -- Step 1: involutivity follows by a direct case split.
  cases a with
  | inl _ => simp [swapEquiv]
  | inr _ => simp [swapEquiv]

lemma swapLetter_ne_self (p : Sum Unit Unit × Bool) : swapLetter p ≠ p := by
  -- Step 1: compare the first coordinates of the two pairs.
  intro h
  have := congrArg Prod.fst h
  exact (swapEquiv_ne_self p.1) <| by simpa [swapLetter] using this

lemma swapEquiv_comp_eq_id : swapEquiv ∘ swapEquiv = id := by
  -- Step 1: expand the composition pointwise.
  funext a; exact swapEquiv_comp_self a

lemma map_swap_word_eq_self_iff_nil
    (L : List (Sum Unit Unit × Bool)) :
    (L.map swapLetter = L) ↔ L = [] := by
  -- Step 1: split on whether the list is empty.
  cases L with
  | nil =>
      -- Step 1.1: the empty list is fixed.
      simp
  | cons x xs =>
      -- Step 1.2: for a non-empty list, compare heads to derive a contradiction.
      constructor
      · intro h
        have hx : swapLetter x = x := by
          -- Step 1.2.1: compare heads via `List.head?`.
          have := congrArg List.head? h
          simpa using this
        -- Step 1.2.2: contradiction with `swapLetter_ne_self`.
        exact False.elim ((swapLetter_ne_self x) hx)
      · intro h
        -- Step 1.2.3: impossible direction because `L` cannot reduce to `[]`.
        exact False.elim (by cases h)

lemma swapAut_apply_twice (g : CounterexampleGroup) :
    swapAutCounter (swapAutCounter g) = g := by
  -- Step 1: use the compositional property of `FreeGroup.map`.
  have h := FreeGroup.map.comp (x := g) (f := swapEquiv) (g := swapEquiv)
  have h' :
      swapAutCounter (swapAutCounter g) =
        FreeGroup.map (swapEquiv ∘ swapEquiv) g := by
    -- Step 1.1: rewrite the two occurrences of `swapAutCounter`.
    simpa [swapAutCounter] using h
  -- Step 2: simplify the composition `swapEquiv ∘ swapEquiv` to the identity.
  have hcomp := swapEquiv_comp_eq_id
  simpa [hcomp, FreeGroup.map.id] using h'

lemma swapAut_fixed_point (g : CounterexampleGroup) :
    swapAutCounter g = g → g = 1 := by
  -- Step 1: translate the equality of elements to the equality of reduced words.
  intro h
  have hmap :
      (swapAutCounter g).toWord =
        g.toWord.map swapLetter := by
    -- Step 1.1: describe `toWord` after applying the automorphism.
    change (FreeGroup.map swapEquiv g).toWord =
      g.toWord.map swapLetter
    simpa [swapLetter] using
      (FreeGroup.toWord_map_of_injective (α := Sum Unit Unit)
        (β := Sum Unit Unit) (f := swapEquiv) swapEquiv.injective g)
  have hword := congrArg FreeGroup.toWord h
  have hword' : g.toWord.map swapLetter = g.toWord := by
    -- Step 1.2: combine the two equalities above.
    simpa [hmap] using hword
  -- Step 2: the only reduced word fixed by `swapLetter` is the empty word.
  have hnil : g.toWord = [] := (map_swap_word_eq_self_iff_nil _).1 hword'
  -- Step 3: convert the empty reduced word back to the identity element.
  simpa [FreeGroup.toWord_eq_nil_iff] using hnil

lemma swapAut_fixed_points :
    ∀ g : CounterexampleGroup, swapAutCounter g = g ↔ g = 1 := by
  -- Step 1: use the previous lemma for the forward direction and reflexivity for the reverse.
  intro g
  constructor
  · -- Step 1.1: apply `swapAut_fixed_point`.
    exact swapAut_fixed_point g
  · -- Step 1.2: the identity is trivially fixed by any automorphism.
    intro hg
    simp [hg]

lemma swapAut_involutive :
    ∀ g : CounterexampleGroup, swapAutCounter (swapAutCounter g) = g :=
  swapAut_apply_twice

lemma of_inl_mul_of_inr_ne :
    (FreeGroup.of (Sum.inl ()) * FreeGroup.of (Sum.inr ())) ≠
      (FreeGroup.of (Sum.inr ()) * FreeGroup.of (Sum.inl ())) := by
  -- Step 2: compute the reduced words of `x` and `y`.
  set gL : Sum Unit Unit := Sum.inl ()
  set gR : Sum Unit Unit := Sum.inr ()
  have hx :
      (FreeGroup.of gL).toWord =
        [((gL, true) : Sum Unit Unit × Bool)] :=
    rfl
  have hy :
      (FreeGroup.of gR).toWord =
        [((gR, true) : Sum Unit Unit × Bool)] :=
    rfl
  -- Step 3: record that the concatenated words stay reduced.
  have hx_single :
      IsReduced [((gR, true) : Sum Unit Unit × Bool)] :=
    (FreeGroup.IsReduced.singleton (a := (gR, true)))
  have hy_single :
      IsReduced [((gL, true) : Sum Unit Unit × Bool)] :=
    (FreeGroup.IsReduced.singleton (a := (gL, true)))
  have hxy :
      IsReduced
        ([((gL, true) : Sum Unit Unit × Bool), ((gR, true) : Sum Unit Unit × Bool)] :
          List (Sum Unit Unit × Bool)) := by
    -- Step 3.1: the first components are different, so there is no cancellation.
    refine (FreeGroup.isReduced_cons_cons).2 ?_
    refine ⟨?_, hx_single⟩
    intro h
    cases h
  have hyx :
      IsReduced
        ([((gR, true) : Sum Unit Unit × Bool), ((gL, true) : Sum Unit Unit × Bool)] :
          List (Sum Unit Unit × Bool)) := by
    -- Step 3.2: the same argument in the reversed order.
    refine (FreeGroup.isReduced_cons_cons).2 ?_
    refine ⟨?_, hy_single⟩
    intro h
    cases h
  -- Step 4: express the reduced words of the products.
  have hxy_word :
      ((FreeGroup.of gL * FreeGroup.of gR).toWord) =
        [((gL, true) : Sum Unit Unit × Bool),
          ((gR, true) : Sum Unit Unit × Bool)] := by
    -- Step 4.1: expand `toWord_mul` and simplify via `hx`, `hy`, and `hxy`.
    simp [FreeGroup.toWord_mul, hx, hy, hxy.reduce_eq]
  have hyx_word :
      ((FreeGroup.of gR * FreeGroup.of gL).toWord) =
        [((gR, true) : Sum Unit Unit × Bool),
          ((gL, true) : Sum Unit Unit × Bool)] := by
    -- Step 4.2: similar computation for the reversed product.
    simp [FreeGroup.toWord_mul, hx, hy, hyx.reduce_eq]
  -- Step 5: the two words differ at their heads.
  have hwords :
      [((gL, true) : Sum Unit Unit × Bool),
        ((gR, true) : Sum Unit Unit × Bool)] ≠
        [((gR, true) : Sum Unit Unit × Bool),
          ((gL, true) : Sum Unit Unit × Bool)] := by
    -- Step 5.1: compare heads via `List.head?`.
    intro h
    have := congrArg List.head? h
    simp at this
  -- Step 6: transfer the inequality back to the group using `toWord` injectivity.
  exact fun h =>
    hwords <| by
      -- Step 6.1: apply `toWord` to the assumed equality and specialize.
      have hword := congrArg FreeGroup.toWord h
      rw [hxy_word] at hword
      rw [hyx_word] at hword
      exact hword

theorem Dummit_Foote_exercise_1_6_23_neg :
    ∃ (G : Type) (_ : Group G) (σ : MulAut G),
      (∀ g : G, σ g = g ↔ g = 1) ∧ (∀ g : G, σ (σ g) = g) ∧
        ∃ x y : G, x * y ≠ y * x := by
  -- Step 1: specialize the abstract data to the free group on two generators.
  refine ⟨CounterexampleGroup, inferInstance, swapAutCounter, ?_, ?_, ?_⟩
  · -- Step 2: record that the automorphism is fixed-point-free.
    intro g; exact swapAut_fixed_points g
  · -- Step 3: show that the automorphism squares to the identity.
    intro g; exact swapAut_involutive g
  · -- Step 4: exhibit the two non-commuting generators.
    refine ⟨FreeGroup.of (Sum.inl ()), FreeGroup.of (Sum.inr ()), ?_⟩
    -- Step 4.1: invoke the explicit inequality.
    simpa using of_inl_mul_of_inr_ne

end Proofnet220

/-
With the missing finiteness assumption reinstated, the classical proof works:
`σ` must agree with inversion, which is a group automorphism precisely when the
group is abelian.  The next theorem formalizes this corrected statement.
-/

theorem Dummit_Foote_exercise_1_6_23_corrected {G : Type*} [Group G] [Finite G]
    (σ : MulAut G) (hs : ∀ g : G, σ g = g ↔ g = 1)
    (hs2 : ∀ g : G, σ (σ g) = g) :
    ∀ x y : G, x * y = y * x := by
  -- Step 1: view `σ` as the associated monoid homomorphism.
  let φ : G →* G := σ.toMonoidHom
  -- Step 2: verify that `φ` is fixed-point-free in the `MonoidHom` sense.
  have hfree : MonoidHom.FixedPointFree φ := by
    -- Step 2.1: transfer the given equivalence to the required implication.
    intro g hg
    exact (hs g).1 hg
  -- Step 3: express involutivity as a statement about the underlying function.
  have hinv : Function.Involutive φ := by
    -- Step 3.1: `hs2` already states the needed property.
    intro g
    simpa using hs2 g
  -- Step 4: commute any two elements using the dedicated lemma.
  intro x y
  -- Step 4.1: specialize the commuting statement to `x` and `y`.
  have hx :
      Commute x y :=
    MonoidHom.FixedPointFree.commute_all_of_involutive
      (φ := φ) hfree hinv x y
  -- Step 4.2: rewrite `Commute` as the desired equality.
  simpa using hx
