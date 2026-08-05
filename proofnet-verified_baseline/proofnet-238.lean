import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $|G|=6545$ then $G$ is not simple.
-/

/-Informal Proof

Since $|G|=132=2^{2}.3.11$, $G$ has $2-$Sylow subgroup of order $4$, as well as $11-$Sylow subgroup of order $11$, and $3-$Sylow subgroup of order $3$. Now, we count the number of such subgroups. Let $n_{11}$ be the number of  $11-$Sylow subgroup and $n_{3}$ be the number of  $3-$Sylow subgroup. Now $n_{11}=1+11k$ where $1+11k|12$. The choices for $k$ are $0$ or $1$. If $k=0$, there is only one $11-$Sylow subgroup and hence normal. So, assume now, that there are $12$ $11-$Sylow subgroup(for $k=1$). Now we look at $3-$ Sylow subgroups. $n_{3}=1+3k| 44$. So choice for $k$ are $0$, $1$, and $7$. If $k=0$, there is only one $3-$Sylow subgroup and hence normal. So, assume now, that there are $4$ $2-$Sylow subgroup (for $k=3$). Now we claim that simultaneously, there cannot be $12$ $11-$Sylow subgroup and $4$ $3-$Sylow subgroups provided there is more than one $2-$Sylow subgroups. So, either $2-$Sylow subgroup is normal or if not, then, either $11-$Sylow subgroup is normal being unique, or  the $3-$Sylow subgroup is normal(We don't consider the possibility of $22$ $3-$Sylow subgroup because of obvious reason). Now, to prove the claim, we observe that there are $120$ elements of order $11$. Also there are $8$ elements of order $3$. So we already get $120+8+1=129$ distinct elements in the group. Let us count the number of $2-$Sylow subgroups in $G$. $n_{2}=1+2k|33$. The possibilities for $k$ are $0$, $1$, $5$, $16$. Now, assume there is more than one $2-$Sylow subgroups. Let $H_{1}$ and $H_{2}$ be two distinct  $2-$Sylow subgroup. Now $|H_{1}|=4$. So we already get $129+3=132$ distinct elements in the group. Now $H_{2}$ being distinct from $H_{1}$, has at least one element which is not in $H_{1}$. This adds one more element in the group, at the least. Now already we have number of elements in the group exceeding the number of element in $G$. This gives a contradiction and proves the claim.
Hence $G$ is not simple.
-/

theorem Dummit_Foote_exercise_4_5_19 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 6545) : ¬ IsSimpleGroup G := by
  classical
  /- Step 1: observe that the concrete number `6545` is squarefree
     (product of the distinct primes 5, 7, 11, and 17). -/
  have hSquarefree6545 : Squarefree 6545 := by native_decide
  /- Step 2: transport the squarefreeness certificate to `G` using the
     provided cardinality identity `hG`. -/
  have hSquarefreeG : Squarefree (Nat.card G) := by
    -- Substep 2.1: rewrite `Nat.card G` as `card G` and then as `6545`.
    simpa [Nat.card_eq_fintype_card, hG] using hSquarefree6545
  /- Step 3: from squarefree order we know every Sylow subgroup of `G`
     is cyclic, i.e. `G` is a Z-group. -/
  have hZ : IsZGroup G := IsZGroup.of_squarefree (G := G) hSquarefreeG
  -- Substep 3.1: register the Z-group structure so typeclass search can use it.
  haveI : IsZGroup G := hZ
  /- Step 4: finite Z-groups are solvable; record this as a hypothesis. -/
  have hSolv : IsSolvable G := inferInstance
  /- Step 5: assume, for contradiction, that `G` were simple. -/
  intro hSimple
  /- Step 6: in a simple group, solvability is equivalent to commutativity,
     so the multiplication on `G` is commutative. -/
  have hcomm : ∀ a b : G, a * b = b * a :=
    (IsSimpleGroup.comm_iff_isSolvable (G := G)).2 hSolv
  -- Substep 6.1: register commutativity as an instance (avoids rebuilding the whole structure).
  haveI : IsMulCommutative G := ⟨⟨hcomm⟩⟩
  -- Substep 6.2: keep the simplicity assumption as an instance for convenience.
  haveI : IsSimpleGroup G := hSimple
  /- Step 7: pick a Sylow 5-subgroup; it exists because 5 is prime. -/
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  classical
  let P5 : Sylow 5 G := Classical.choice (inferInstance : Nonempty (Sylow 5 G))
  -- Substep 7.1: compute its cardinality (it must be 5, since 5 divides `|G|` only once).
  have hfac5 : Nat.factorization (card G) 5 = 1 := by
    have : Nat.factorization 6545 5 = 1 := by native_decide
    simpa [hG] using this
  have hP5card : Fintype.card P5 = 5 := by
    -- First rewrite the multiplicity, then simplify the resulting `5 ^ 1`.
    have h := (P5.card_eq_multiplicity (G := G))
    -- `h : Nat.card P5 = 5 ^ Nat.factorization (card G) 5`
    have h' : Nat.card P5 = 5 ^ 1 := by simpa [hfac5] using h
    -- Convert `Nat.card` to `Fintype.card` and simplify `5 ^ 1`.
    simpa [Nat.card_eq_fintype_card] using h'
  -- Substep 7.2: `P5` is nontrivial and proper.
  have hP5_ne_bot : (P5 : Subgroup G) ≠ ⊥ := by
    intro h
    have := congrArg (fun H : Subgroup G => Fintype.card H) h
    -- `Nat.card (⊥ : Subgroup G) = 1`, contradicting `hP5card = 5`.
    simp [hP5card] at this
  have hP5_ne_top : (P5 : Subgroup G) ≠ ⊤ := by
    intro h
    have := congrArg (fun H : Subgroup G => Fintype.card H) h
    -- `Nat.card (⊤ : Subgroup G) = |G| = 6545`, again contradicting `hP5card = 5`.
    simp [hG, hP5card] at this
  /- Step 8: in a commutative group every subgroup is normal, so the simple-group
     axiom forces `P5` to be either `⊥` or `⊤`, contradicting Substep 7.2. -/
  have hP5_normal : (P5 : Subgroup G).Normal := by
    -- In an abelian group conjugation is trivial, so every subgroup is normal.
    refine ⟨?_⟩
    intro x hx g
    -- `g * x * g⁻¹ = x` by commutativity.
    have hconj : g * x * g⁻¹ = x := by
      calc
        g * x * g⁻¹ = x * g * g⁻¹ := by
          simp [mul_comm, mul_assoc]
        _ = x := by simp
    simpa [hconj] using hx
  have hBotOrTop := IsSimpleGroup.eq_bot_or_eq_top_of_normal (P5 : Subgroup G) hP5_normal
  cases hBotOrTop with
  | inl h => exact hP5_ne_bot h
  | inr h => exact hP5_ne_top h
