import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Suppose $X$ is a nonempty complete metric space, and $\left\{G_{n}\right\}$ is a sequence of dense open sets of $X$. Prove Baire's theorem, namely, that $\bigcap_{1}^{\infty} G_{n}$ is not empty.
-/

/-Informal Proof

Let $F_n$ be the complement of $G_n$, so that $F_n$ is closed and contains no open sets. We shall prove that any nonempty open set $U$ contains a point not in any $F_n$, hence in all $G_n$. To this end, we note that $U$ is not contained in $F_1$, so that there is a point $x_1 \in U \backslash F_1$. Since $U \backslash F_1$ is open, there exists $r_1>0$ such that $B_1$, defined as the open ball of radius $r_1$ about $x_1$, is contained in $U \backslash F_1$. Let $E_1$ be the open ball of radius $\frac{r_1}{2}$ about $x_1$, so that the closure of $E_1$ is contained in $B_1$. Now $F_2$ does not contain $E_1$, and so we can find a point $x_2 \in E_1 \backslash F_2$. Since $E_1 \backslash F_2$ is an open set, there exists a positive number $r_2$ such that $B_2$, the open ball of radius $R_2$ about $x_2$, is contained in $E_1 \backslash F_2$, which in turn is contained in $U \backslash\left(F_1 \cup F_2\right)$. We let $E_2$ be the open ball of radius $\frac{r_2}{2}$ about $x_2$, so that $\bar{E}_2 \subseteq B_2$. Proceeding in this way, we construct a sequence of open balls $E_j$, such that $E_j \supseteq \bar{E}_{j+1}$, and the diameter of $E_j$ tends to zero. By the previous exercise, there is a point $x$ belonging to all the sets $\bar{E}_j$, hence to all the sets $U \backslash\left(F_1 \cup F_2 \cup \cdots \cup F_n\right)$. Thus the point $x$ belongs to $U \cap\left(\cap_1^{\infty} G_n\right)$.
-/

theorem Rudin_exercise_3_22 (X : Type*) [MetricSpace X] [CompleteSpace X] [Nonempty X]
  (G : ℕ → Set X) (hG : ∀ n, IsOpen (G n) ∧ Dense (G n)) :
  ∃ x, ∀ n, x ∈ G n := by
  classical
  -- Step 1: Isolate the openness information for each `G n` so it can be reused uniformly.
  have hOpen : ∀ n, IsOpen (G n) := by
    -- Step 1.1: Fix an arbitrary natural number `n`.
    intro n
    -- Step 1.2: Project the first component (openness) from the hypothesis `hG n`.
    exact (hG n).1
  -- Step 2: Isolate the density information for each `G n` for later application of Baire.
  have hDenseEach : ∀ n, Dense (G n) := by
    -- Step 2.1: Fix an arbitrary natural number `n`.
    intro n
    -- Step 2.2: Project the second component (density) from `hG n`.
    exact (hG n).2
  -- Step 3: Apply Baire's theorem to deduce that the full intersection is dense.
  have hDenseInter : Dense (⋂ n, G n) :=
    dense_iInter_of_isOpen_nat hOpen hDenseEach
  -- Step 4: Use the density (together with `Nonempty X`) to extract an actual point in the intersection.
  obtain ⟨x, hx⟩ := hDenseInter.nonempty
  -- Step 5: Translate membership in the intersection into membership in each individual `G n`.
  have hx_mem : ∀ n, x ∈ G n := by
    -- Step 5.1: Expand the definition of membership in an indexed intersection.
    exact Set.mem_iInter.mp hx
  -- Step 6: Package the constructed point and its membership property to conclude.
  exact ⟨x, hx_mem⟩
