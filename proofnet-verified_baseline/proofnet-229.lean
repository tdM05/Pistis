import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that quotient groups of a solvable group are solvable.
-/

/-Informal Proof

Next, note that
$$
H_i=G_i \cap H=\left(G_i \cap G_{i+1}\right) \cap H=G_i \cap H_{i+1} .
$$
By the Second Isomorphism Theorem, we then have
$$
H_{i+1} / H_i=H_{i+1} /\left(H_{i+1} \cap G_i\right) \cong H_{i+1} G_i / G_i \leq G_{i+1} / G_i .
$$
Since $H_{i+1} / H_i$ is isomorphic to a subgroup of the abelian group $G_{i+1} / G_i$, it follows that $H_{i+1} / H_i$ is also abelian. This completes the proof that $H$ is solvable.
Next, let $N \unlhd G$. For each $i$, define
$$
N_i=G_i N, \quad 0 \leq i \leq n .
$$
Now let $g \in N_{i+1}$, where $g=g_0 n_0$ with $g_0 \in G_{i+1}$ and $n_0 \in N$. Also let $x \in N_i$, where $x=g_1 n_1$ with $g_1 \in G_i$ and $n_1 \in N$. Then
$$
g x g^{-1}=g_0 n_0 g_1 n_1 n_0^{-1} g_0^{-1} .
$$
Now, since $N$ is normal in $G, N g=g N$, so $n_0 g_1=g_1 n_2$ for some $n_2 \in N$. Then
$$
g x g^{-1}=g_0 g_1\left(n_2 n_1 n_0^{-1}\right) g_0^{-1}=g_0 g_1 n_3 g_0^{-1}
$$
for some $n_3 \in N$. Then $n_3 g_0^{-1}=g_0^{-1} n_4$ for some $n_4 \in N$. And $g_0 g_1 g_0^{-1} \in G_i$ since $G_i \unlhd G_{i+1}$, so
$$
g x g^{-1}=g_0 g_1 g_0^{-1} n_4 \in N_i .
$$
This shows that $N_i \unlhd N_{i+1}$. So by the Lattice Isomorphism Theorem, we have $N_{i+1} / N \unlhd N_i / N$. This shows that
$$
1=N_0 / N \unlhd N_1 / N \unlhd N_2 / N \unlhd \cdots \unlhd N_n / N=G / N .
$$
Moreover, the Third Isomorphism Theorem says that
$$
\left(N_{i+1} / N\right) /\left(N_i / N\right) \cong N_{i+1} / N_i,
$$
so the proof will be complete if we can show that $N_{i+1} / N_i$ is abelian.
Let $x, y \in N_{i+1} / N_i$. Then
$$
x=\left(g_0 n_0\right) N_i \quad \text { and } \quad y=\left(g_1 n_1\right) N_i
$$
for some $g_0, g_1 \in G_{i+1}$ and $n_0, n_1 \in N$. We have
$$
\begin{aligned}
x y x^{-1} y^{-1} & =\left(g_0 n_0\right)\left(g_1 n_1\right)\left(g_0 n_0\right)^{-1}\left(g_1 n_1\right)^{-1} N_i \\
& =g_0 n_0 g_1 n_1 n_0^{-1} g_0^{-1} n_1^{-1} g_1^{-1} N_i .
\end{aligned}
$$
Since $N \unlhd G, g N=N g$ for any $g \in G$, so we can find $n_2 \in N$ such that
$$
x y x^{-1} y^{-1}=g_0 g_1 g_0^{-1} g^{-1} n_2 N_i .
$$
Now $N_i=G_i N=N G_i$ since $N \unlhd G$ (see Proposition 14 and its corollary). Therefore
$$
n_2 N_i=n_2 N G_i=N G_i=G_i N
$$
and we get
$$
x y x^{-1} y^{-1}=g_0 g_1 g_0^{-1} g^{-1} G_i N=G_i N .
$$
So $x y x^{-1} y^{-1}=1 N_i$ or $x y=y x$. This completes the proof that $G / N$ is solvable.
-/

theorem Dummit_Foote_exercise_3_4_5b {G : Type*} [Group G] [IsSolvable G]
  (H : Subgroup G) [Normal H] :
  IsSolvable (G ⧸ H) := by
  -- Step 0: Switch to classical logic so that we can freely use choice in surjectivity arguments.
  classical
  -- Step 1: Introduce the canonical quotient homomorphism π : G →* G ⧸ H.
  let π : G →* G ⧸ H := QuotientGroup.mk' H
  -- Step 1.1: Record that π is surjective by construction of the quotient group.
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective H
  -- Step 2: Use the general lemma saying that surjective homomorphic images of solvable groups
  -- remain solvable; apply it to π with the given hypothesis `[IsSolvable G]`.
  have hsol : IsSolvable (G ⧸ H) :=
    solvable_of_surjective (G := G) (G' := G ⧸ H) (f := π) hπ
  -- Step 3: Conclude by returning the solvability information obtained in Step 2.
  exact hsol
