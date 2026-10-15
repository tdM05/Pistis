import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

/-!
We start with a small helper lemma that allows us to convert a `ContinuousOn` hypothesis on a set
into an honest `Continuous` map defined on the corresponding subtype.
-/

lemma ContinuousOn.continuous_subtype {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {s : Set α} {f : α → β} (hf : ContinuousOn f s) :
    Continuous fun x : s => f x := by
  classical
  refine continuous_iff_continuousAt.2 ?_
  intro x
  /- Step 1: The inclusion `s → α` is continuous at `x`, so it sends `𝓝 x` into `𝓝[s] x`. -/
  have hx_sub :
      Tendsto (fun y : s => (y : α)) (𝓝 x) (𝓝[s] (x : α)) := by
    refine (tendsto_def.2 ?_)
    change Filter.map (fun y : s => (y : α)) (𝓝 x) ≤ 𝓝[s] (x : α)
    have hx_comap :
        𝓝 x ≤ Filter.comap (fun y : s => (y : α)) (𝓝[s] (x : α)) := by
      simp [nhds_subtype_eq_comap_nhdsWithin (s := s) (x := x)]
    exact (Filter.map_le_iff_le_comap).2 hx_comap
  /- Step 2: Compose the previous step with the `ContinuousWithinAt` information coming from `hf`. -/
  have hx_cont :
      Tendsto f (𝓝[s] (x : α)) (𝓝 (f x)) := by
    simpa [ContinuousWithinAt] using hf x.1 x.2
  simpa using hx_cont.comp hx_sub


/-Informal Statement

If $f$ is a real continuous function defined on a closed set $E \subset \mathbb{R}$, prove that there exist continuous real functions $g$ on $\mathbb{R}$ such that $g(x)=f(x)$ for all $x \in E$.
-/

/-Informal Proof

Following the hint, let the complement of $E$ consist of a countable collection of finite open intervals $\left(a_k, b_k\right)$ together with possibly one or both of the the semi-infinite intervals $(b,+\infty)$ and $(-\infty, a)$. The function $f(x)$ is already defined at $a_k$ and $b_k$, as well as at $a$ and $b$ (if these last two points exist). Define $g(x)$ to be $f(b)$ for $x>b$ and $f(a)$ for $x<a$ if $a$ and $b$ exist. On the interval $\left(a_k, b_k\right)$ let
$$
g(x)=f\left(a_k\right)+\frac{x-a_k}{b_k-a_k}\left(f\left(b_k\right)-f\left(a_k\right)\right) .
$$
Of course we let $g(x)=f(x)$ for $x \in E$. It is now fairly clear that $g(x)$ is continuous. A rigorous proof proceeds as follows. Let $\varepsilon>0$. To choose $\delta>0$ such that $|x-u|<\delta$ implies $|g(x)-g(u)|<\varepsilon$, we consider three cases.
i. If $x>b$, let $\delta=x-b$. Then if $|x-u|<\delta$, it follows that $u>b$ also, so that $g(u)=f(b)=g(x)$, and $|g(u)-g(x)|=0<\varepsilon$. Similarly if $x<a$, let $\delta=a-x$
ii. If $a_k<x<b_k$ and $f\left(a_k\right)=f\left(b_k\right)$, let $\delta=\min \left(x-a_k, b_k-x\right)$. Since $|x-u|<\delta$ implies $a_k<u<b_k$, so that $g(u)=f\left(a_k\right)=f\left(b_k\right)=g(x)$, we again have $|g(x)-g(u)|=0<\varepsilon$. If $a_k<x<b_k$ and $f\left(a_k\right) \neq f\left(b_k\right)$, let $\delta=\min \left(x-a_k, b_k-x, \frac{\left(b_k-a_k\right) \varepsilon}{\left|f\left(b_k\right)-f\left(a_k\right)\right|}\right)$. Then if $|x-u|<\delta$, we again have $a_k<u<b_k$ and so
$$
|g(x)-g(u)|=\frac{|x-u|}{b_k-a_k}\left|f\left(b_k\right)-f\left(a_k\right)\right|<\varepsilon .
$$
iii. If $x \in E$, let $\delta_1$ be such that $|f(u)-f(x)|<\varepsilon$ if $u \in E$ and $|x-u|<\delta_1$. (Subcase a). If there are points $x_1 \in E \cap\left(x-\delta_1, x\right)$ and $x_2 \in E \cap\left(x, x+\delta_1\right)$, let $\delta=\min \left(x-x_1, x_2-x\right)$. If $|u-x|<\delta$ and $u \in E$, then $|f(u)-f(x)|<\varepsilon$ by definition of $\delta_1$. if $u \notin E$, then, since $x_1, x$, and $x_2$ are all in $E$, it follows that $u \in\left(a_k, b_k\right)$, where $a_k \in E, b_k \in E$, and $\left|a_k-x\right|<\delta$ and $\left|b_k-x\right|<\delta$, so that $\left|f\left(a_k\right)-f(x)\right|<\varepsilon$ and $\left|f\left(b_k\right)-f(x)\right|<\varepsilon$. If $f\left(a_k\right)=f\left(b_k\right)$, then $f(u)=f\left(a_k\right)$ also, and we have $|f(u)-f(x)|<\varepsilon$. If $f\left(a_k\right) \neq f\left(b_k\right)$, then
$$
\begin{aligned}
|f(u)-f(x)| & =\left|f\left(a_k\right)-f(x)+\frac{u-a_k}{b_k-a_k}\left(f\left(b_k\right)-f\left(a_k\right)\right)\right| \\
& =\left|\frac{b_k-u}{b_k-a_k}\left(f\left(a_k\right)-f(x)\right)+\frac{u-a_k}{b_k-a_k}\left(f\left(b_k\right)-f(x)\right)\right| \\
& <\frac{b_k-u}{b_k-a_k} \varepsilon+\frac{u-a_k}{b_k-a_k} \varepsilon \\
& =\varepsilon
\end{aligned}
$$
(Subcase b). Suppose $x_2$ does not exist, i.e., either $x=a_k$ or $x=a_k$ and $b_k>a_k+\delta_1$. Let us consider the second of these cases and show how to get $|f(u)-f(x)|<\varepsilon$ for $x<u<x+\delta$. If $f\left(a_k\right)=f\left(b_k\right)$, let $\delta=\delta_1$. If $u>x$ we have $a_k<u<b_k$ and $f(u)=f\left(a_k\right)=f(x)$. If $f\left(a_k\right) \neq f\left(b_k\right)$, let $\delta=$ $\min \left(\delta_1, \frac{\left(b_k-a_k\right) \varepsilon}{\left|f\left(b_k\right)-f\left(a_k\right)\right|}\right)$. Then, just as in Subcase a, we have $|f(u)-f(x)|<\varepsilon$.
The case when $x=b_k$ for some $k$ and $a_k<x-\delta_1$ is handled in exactly the same way.
-/

theorem Rudin_exercise_4_5a
  (f : ℝ → ℝ)
  (E : Set ℝ)
  (h₁ : IsClosed E)
  (h₂ : ContinuousOn f E)
  : ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x := by
  classical
  /- Step 1: Turn the `ContinuousOn` hypothesis into a bundled continuous map on the subtype `E`. -/
  have hf_subtype : Continuous fun x : E => f x :=
    h₂.continuous_subtype
  /- Step 1.1: Package the subtype function as a `ContinuousMap` so that we can invoke Tietze. -/
  let fSub : C(E, ℝ) := ⟨fun x : E => f x, hf_subtype⟩
  /- Step 2: Apply the Tietze extension theorem on ℝ to obtain a global continuous map `gMap`. -/
  obtain ⟨gMap, hgRestr⟩ :=
    ContinuousMap.exists_restrict_eq (X := ℝ) (Y := ℝ) (s := E) h₁ fSub
  /- Step 2.1: View `gMap` as the desired function `g : ℝ → ℝ`. -/
  refine ⟨gMap, ?_, ?_⟩
  /- Step 3: Record that `gMap` is continuous as a map on all of ℝ. -/
  · /- Step 3.1: Use the bundled continuity of `gMap`. -/
    simpa using gMap.continuous
  /- Step 4: Show that `gMap` agrees with `f` on every point of `E`. -/
  · intro x hx
    /- Step 4.1: Evaluate the identity `gMap.restrict E = fSub` at the subtype point `⟨x, hx⟩`. -/
    have hxEq :=
      congrArg (fun h : C(E, ℝ) => h ⟨x, hx⟩) hgRestr
    /- Step 4.2: Simplify both sides back to unbundled functions. -/
    simpa [fSub, ContinuousMap.restrict_apply] using hxEq.symm
