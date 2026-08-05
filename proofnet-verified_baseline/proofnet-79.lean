import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $G$ is an abelian group and if $G$ has an element of order $m$ and one of order $n$, where $m$ and $n$ are relatively prime, prove that $G$ has an element of order $mn$.
-/

/-Informal Proof

Let $G$ be an abelian group, and let $a$ and $b$ be elements in $G$ of order $m$ and $n$, respectively, where $m$ and $n$ are relatively prime. We will show that the product $ab$ has order $mn$ in $G$, which will prove that $G$ has an element of order $mn$.

To show that $ab$ has order $mn$, let $k$ be the order of $ab$ in $G$. We have $a^m = e$, $b^n = e$, and $(ab)^k = e$, where $e$ denotes the identity element of $G$. Since $G$ is abelian, we have
$$(ab)^{mn} = a^{mn}b^{mn} = e \cdot e = e.$$
Thus, $k$ is a divisor of $mn$.

Now, observe that $a^k = b^{-k}$. Since $m$ and $n$ are relatively prime, there exist integers $x$ and $y$ such that $mx + ny = 1$. Taking $kx$ on both sides of the equation, we get $a^{kx} = b^{-kx}$, or equivalently, $(a^k)^x = (b^k)^{-x}$. It follows that $a^{kx} = (a^m)^{xny} = e$, and similarly, $b^{ky} = (b^n)^{mxk} = e$. Therefore, $m$ divides $ky$ and $n$ divides $kx$. Since $m$ and $n$ are relatively prime, it follows that $mn$ divides $k$. Hence, $k = mn$, and $ab$ has order $mn$ in $G$. This completes the proof.
-/

theorem Herstein_exercise_2_6_15 {G : Type*} [CommGroup G] {m n : ℕ}
  (hm : ∃ (g : G), orderOf g = m)
  (hn : ∃ (g : G), orderOf g = n)
  (hmn : m.Coprime n) :
  ∃ (g : G), orderOf g = m * n := by
  classical
  -- Step 1: Extract an element whose order is the given natural number `m`.
  obtain ⟨g₁, hg₁⟩ := hm
  -- Step 1.1: Extract an element whose order is the given natural number `n`.
  obtain ⟨g₂, hg₂⟩ := hn
  -- Step 2: In a commutative group every pair of elements commutes, which we record for `g₁` and `g₂`.
  have hcomm : Commute g₁ g₂ := by
    -- Step 2.1: Use the helper lemma `Commute.all` specialised to `g₁` and `g₂`.
    simpa using (Commute.all g₁ g₂)
  -- Step 3: Transport the assumed coprimality of `m` and `n` to the orders of `g₁` and `g₂`.
  have hcop : (orderOf g₁).Coprime (orderOf g₂) := by
    -- Step 3.1: Rewrite the orders with the equations `orderOf g₁ = m` and `orderOf g₂ = n`.
    simpa [hg₁, hg₂] using hmn
  -- Step 4: Compute the order of the product `g₁ * g₂` using the coprime-order lemma for commuting elements.
  have horder_product :
      orderOf (g₁ * g₂) = orderOf g₁ * orderOf g₂ := by
    -- Step 4.1: Apply the lemma `orderOf_mul_eq_mul_orderOf_of_coprime` with the previously collected data.
    simpa using hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  -- Step 5: Package the element `g₁ * g₂` together with the computed order to satisfy the existential claim.
  refine ⟨g₁ * g₂, ?_⟩
  -- Step 5.1: Replace the orders of `g₁` and `g₂` by `m` and `n` to obtain the desired equality.
  simpa [hg₁, hg₂] using horder_product
