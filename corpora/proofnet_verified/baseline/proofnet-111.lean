import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

A map $f: X \rightarrow Y$ is said to be an open map if for every open set $U$ of $X$, the set $f(U)$ is open in $Y$. Show that $\pi_{1}: X \times Y \rightarrow X$ and $\pi_{2}: X \times Y \rightarrow Y$ are open maps.
-/

/-Informal Proof

Exercise 16.4. Let $U \times V$ be a (standard) basis element for $X \times Y$, so that $U$ is open in $X$ and $V$ is open in $Y$. Then $\pi_1(U \times V)=U$ is open in $X$ and $\pi_2(U \times V)=V$ is open in $Y$. Since arbitrary maps and unions satisfy $f\left(\bigcup_\alpha W_\alpha\right)=\bigcup_\alpha f\left(W_\alpha\right)$, it follows that $\pi_1$ and $\pi_2$ are open maps.
-/

theorem Munkres_exercise_16_4 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (π₁ : X × Y → X)
  (π₂ : X × Y → Y)
  (h₁ : π₁ = Prod.fst)
  (h₂ : π₂ = Prod.snd) :
  IsOpenMap π₁ ∧ IsOpenMap π₂ := by
  constructor
  · -- Step 1: Our goal is to show that `π₁` is an open map.
    -- Step 1.1: Rewrite `π₁` using `h₁` so the goal becomes the standard projection `Prod.fst`.
    -- Step 1.2: Apply the library lemma `isOpenMap_fst`, which establishes that `Prod.fst` is open.
    simpa [h₁] using (isOpenMap_fst : IsOpenMap (Prod.fst : X × Y → X))
  · -- Step 2: Our goal is to show that `π₂` is an open map.
    -- Step 2.1: Rewrite `π₂` using `h₂` so the goal becomes the standard projection `Prod.snd`.
    -- Step 2.2: Apply the library lemma `isOpenMap_snd`, which establishes that `Prod.snd` is open.
    simpa [h₂] using (isOpenMap_snd : IsOpenMap (Prod.snd : X × Y → Y))
