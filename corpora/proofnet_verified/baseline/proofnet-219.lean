import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $A$ and $B$ be groups. Prove that $A \times B \cong B \times A$.
-/

/-Informal Proof

We know from set theory that the mapping $\varphi: A \times B \rightarrow B \times A$ given by $\varphi((a, b))=(b, a)$ is a bijection with inverse $\psi: B \times A \rightarrow A \times B$ given by $\psi((b, a))=(a, b)$. Also $\varphi$ is a homomorphism, as we show below.
Let $a_1, a_2 \in A$ and $b_1, b_2 \in B$. Then
$$
\begin{aligned}
\varphi\left(\left(a_1, b_1\right) \cdot\left(a_2, b_2\right)\right) &=\varphi\left(\left(a_1 a_2, b_1 b_2\right)\right) \\
&=\left(b_1 b_2, a_1 a_2\right) \\
&=\left(b_1, a_1\right) \cdot\left(b_2, a_2\right) \\
&=\varphi\left(\left(a_1, b_1\right)\right) \cdot \varphi\left(\left(a_2, b_2\right)\right)
\end{aligned}
$$
Hence $A \times B \cong B \times A$.
-/

theorem Dummit_Foote_exercise_1_6_11 {A B : Type*} [Group A] [Group B] :
  Nonempty (A × B ≃* B × A) := by
  -- Step 1: Identify the canonical multiplicative equivalence that swaps components of the product group.
  -- Step 1.1: `MulEquiv.prodComm` specializes (under the current typeclass assumptions) to the map `(a, b) ↦ (b, a)` with inverse swapping back.
  -- Step 2: Package this equivalence as an explicit inhabitant of the desired `Nonempty` type.
  exact ⟨MulEquiv.prodComm⟩
