import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $G=\left\{g_{1}, \ldots, g_{n}\right\}$ be a finite group. Prove that the element $N=g_{1}+g_{2}+\ldots+g_{n}$ is in the center of the group ring $R G$.
-/

/-Informal Proof

Let $M=\sum_{i=1}^n r_i g_i$ be an element of $R[G]$. Note that for each $g_i \in G$, the action of $g_i$ on $G$ by conjugation permutes the subscripts. Then we have the following.
$$
\begin{aligned}
N M &=\left(\sum_{i=1}^n g_i\right)\left(\sum_{j=1}^n r_j g_j\right) \\
&=\sum_{j=1}^n \sum_{i=1}^n r_j g_i g_j \\
&=\sum_{j=1}^n \sum_{i=1}^n r_j g_j g_j^{-1} g_i g_j \\
&=\sum_{j=1}^n r_j g_j\left(\sum_{i=1}^n g_j^{-1} g_i g_j\right) \\
&=\sum_{j=1}^n r_j g_j\left(\sum_{i=1}^n g_i\right) \\
&=\left(\sum_{j=1}^n r_j g_j\right)\left(\sum_{i=1}^n g_i\right) \\
&=M N .
\end{aligned}
$$
Thus $N \in Z(R[G])$.
-/

theorem Dummit_Foote_exercise_7_2_12 {R G : Type*} [Ring R] [Group G] [Fintype G] :
  ∑ g : G, MonoidAlgebra.of R G g ∈ center (MonoidAlgebra R G) := by
  -- Step 1: work in a classical setting so that we have
  -- decidable equality on `G` and can use all `Fintype`/`Finsupp`
  -- big-operator lemmas conveniently.
  classical

  -- Step 2: introduce a convenient name for the element
  --   N = ∑ g : G, of R G g
  -- in the group ring `R[G]`.  We keep the original definition so
  -- that we can rewrite back to it at the very end.
  set N : MonoidAlgebra R G := ∑ g : G, MonoidAlgebra.of R G g with hNdef

  -- Step 3: compute the coefficient of an arbitrary group element
  -- `g₀ : G` in `N`.  We will show that every coefficient is equal
  -- to `1 : R`, i.e. `N` is the constant-`1` function on `G`.
  have hNcoeff : ∀ g₀ : G, N g₀ = (1 : R) := by
    -- Step 3.1: fix an arbitrary element `g₀` of the group.
    intro g₀
    -- Step 3.2: using the definition of `N`, it suffices to show that
    -- the finite sum
    --   ∑ g : G, of R G g
    -- has value `1` at `g₀`.  We prove a more general statement for an
    -- arbitrary finite subset `s : Finset G` and then specialize to
    -- `s = Finset.univ`.
    classical
    -- Step 3.2.1: general lemma by induction on `s`.
    have h_general :
        ∀ s : Finset G,
          (∑ m ∈ s, (MonoidAlgebra.of R G m : MonoidAlgebra R G)) g₀ =
            (if g₀ ∈ s then (1 : R) else 0) := by
      -- Induction on the finite set `s`.
      intro s
      refine Finset.induction_on s ?base ?step
      · -- Base case: `s = ∅`.  The sum is `0`, and `g₀ ∉ ∅`.
        -- So both sides are `0`.
        simp
      · -- Inductive step: insert a new element `a` into `s`.
        intro a s ha ih
        -- `ha : a ∉ s`, `ih` is the statement for `s`.
        -- We prove the statement for `insert a s`.
        -- Split into the cases `g₀ = a` and `g₀ ≠ a`.
        by_cases h : g₀ = a
        · -- Step 3.2.1.1: case `g₀ = a`.
          -- Then `g₀ ∉ s` because `a ∉ s`, so `(of R G a) g₀ = 1` and
          -- the contribution from the remaining sum must be `0`.
          subst h
          -- Rewrite the induction hypothesis in terms of `single`.
          have ih' :
              (∑ m ∈ s, (MonoidAlgebra.single m (1 : R) : MonoidAlgebra R G)) g₀ =
                (if g₀ ∈ s then (1 : R) else 0) := by
            simpa [MonoidAlgebra.of] using ih
          -- Since `g₀ ∉ s`, the right-hand side is `0`, so the sum over
          -- `s` evaluates to `0` at `g₀`.
          have hs_zero :
              (∑ m ∈ s, (MonoidAlgebra.single m (1 : R) : MonoidAlgebra R G)) g₀ = 0 := by
            simpa [ha] using ih'
          -- Now expand the sum over `insert g₀ s` and use the previous
          -- observation.
          have :
              (∑ m ∈ insert g₀ s,
                  (MonoidAlgebra.single m (1 : R) : MonoidAlgebra R G)) g₀ =
                1 := by
            -- The new term at `g₀` contributes `1`, the rest contributes
            -- `0`.
            simp [Finset.sum_insert, ha, hs_zero]
          -- On the right-hand side we have `if g₀ ∈ insert g₀ s then 1
          -- else 0 = 1`.  Combining these, the desired equality holds.
          simpa [Finset.mem_insert] using this
        · -- Step 3.2.1.2: case `g₀ ≠ a`.
          -- Here `(of R G a) g₀ = 0`, so the new term does not change
          -- the value of the sum, and membership of `g₀` is unchanged.
          have hne : a ≠ g₀ := by exact ne_comm.mp h
          -- The goal in this branch reduces exactly to the induction
          -- hypothesis (rewritten using `single`).
          have ih' :
              (∑ m ∈ s, (MonoidAlgebra.single m (1 : R) : MonoidAlgebra R G)) g₀ =
                (if g₀ ∈ s then (1 : R) else 0) := by
            simpa [MonoidAlgebra.of] using ih
          -- Now expand the sum over `insert a s`; the new term is `0`
          -- at `g₀` because `g₀ ≠ a`.
          simpa [Finset.sum_insert, ha, MonoidAlgebra.of, Finsupp.single_apply, h, hne,
            Finset.mem_insert] using ih'
    -- Step 3.2.2: apply the general lemma to `s = Finset.univ`.  Since
    -- `g₀ ∈ Finset.univ`, the right-hand side is `1`.
    have h_univ :
        (∑ m ∈ (Finset.univ : Finset G),
          (MonoidAlgebra.of R G m : MonoidAlgebra R G)) g₀ = 1 := by
      simpa using h_general (Finset.univ : Finset G)
    -- Step 3.2.3: rewrite the restricted sum over `Finset.univ` as the
    -- unrestricted sum over all `G`, and translate back to `N`.
    have : (∑ m : G, (MonoidAlgebra.of R G m : MonoidAlgebra R G)) g₀ = 1 := by
      simpa using h_univ
    simpa [N] using this

  -- Step 4: show that `N` lies in the center of `R[G]`.  By the definition
  -- of the (ring) center as a subsemiring, this is equivalent to `N`
  -- commuting multiplicatively with every element of `R[G]`.
  have hcentral : N ∈ center (MonoidAlgebra R G) := by
    -- Step 4.1: expand membership in the center using the lemma
    -- `Subsemiring.mem_center_iff`, which identifies central elements
    -- with those commuting with every element of the ring.
    -- We use the direction
    --   (∀ a, a * N = N * a) → N ∈ center (MonoidAlgebra R G).
    refine (Subsemiring.mem_center_iff (R := MonoidAlgebra R G) (z := N)).2 ?_
    -- Step 4.2: fix an arbitrary element `a` of the group ring and show that
    -- it commutes with `N`.
    intro a
    -- Step 4.3: two elements of `MonoidAlgebra R G` are equal iff all of
    -- their coefficients agree.  The `ext` tactic reduces the problem to
    -- equality of coefficients at each group element `g : G`.
    ext g
    -- At this stage the goal is
    --   ((a * N) g) = ((N * a) g).
    -- Step 4.4: use the convolution formulas `mul_apply_left` and
    -- `mul_apply_right` specialized to groups.  They express the coefficient
    -- of `g` in a product `x * y` as a finite sum over the coefficients
    -- of one factor times suitable values of the other factor.
    --  * `(a * N) g` becomes `a.sum (fun h r => r * N (h⁻¹ * g))`;
    --  * `(N * a) g` becomes `a.sum (fun h r => N (g * h⁻¹) * r)`.
    -- Using `hNcoeff` both `N (h⁻¹ * g)` and `N (g * h⁻¹)` simplify to `1`,
    -- so both sides reduce to `a.sum (fun _ r => r)`.
    -- Step 4.5: expand both products using the convolution formulas and
    -- then simplify using `hNcoeff`.  We treat the two sides separately
    -- to ensure the left-hand side is expressed using a sum over `a`,
    -- while the right-hand side is expressed using a sum over `a` as well.
    -- This makes the final comparison straightforward.
    --
    -- Step 4.5.1: rewrite the left-hand side using `mul_apply_left`.
    have hL :
        (a * N : MonoidAlgebra R G) g =
          a.sum (fun h r => r * N (h⁻¹ * g)) :=
      MonoidAlgebra.mul_apply_left (x := a) (y := N) (g := g)
    -- Step 4.5.2: rewrite the right-hand side using `mul_apply_right`.
    have hR :
        (N * a : MonoidAlgebra R G) g =
          a.sum (fun h r => N (g * h⁻¹) * r) :=
      MonoidAlgebra.mul_apply_right (x := N) (y := a) (g := g)
    -- Step 4.5.3: compare the two expressions term by term, using that
    -- all values of `N` are equal to `1`.
    calc
      (a * N : MonoidAlgebra R G) g
          = a.sum (fun h r => r * N (h⁻¹ * g)) := hL
      _ = a.sum (fun h r => r) := by
        -- Here we replace `N (h⁻¹ * g)` by `1` and simplify.
        -- The inner terms become `r * 1 = r`.
        simp [hNcoeff]
      _ = a.sum (fun h r => (1 : R) * r) := by
        -- Re-introduce an explicit factor `1` on the left, in order to
        -- match the shape appearing on the right-hand side.
        simp
      _ = a.sum (fun h r => N (g * h⁻¹) * r) := by
        -- Replace `1` again by the corresponding value of `N`, namely
        -- `N (g * h⁻¹)`, and simplify.
        simp [hNcoeff]
      _ = (N * a : MonoidAlgebra R G) g := hR.symm

  -- Step 5: translate the statement back from the named element `N` to the
  -- original sum in the statement of the theorem, using the defining
  -- equation `hNdef`.
  simpa [N] using hcentral
