import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology



/-Informal Statement

Suppose that $f$ is holomorphic in an open set $\Omega$. Prove that if $|f|$ is constant, then $f$ is constant.
-/

/-Informal Proof

Let $f(z)=f(x, y)=u(x, y)+i v(x, y)$, where $z=x+i y$.
We first give a mostly correct argument; the reader should pay attention to find the difficulty. Since $|f|=\sqrt{u^2+v^2}$ is constant,
$$
\left\{\begin{array}{l}
0=\frac{\partial\left(u^2+v^2\right)}{\partial x}=2 u \frac{\partial u}{\partial x}+2 v \frac{\partial v}{\partial x} . \\
0=\frac{\partial\left(u^2+v^2\right)}{\partial y}=2 u \frac{\partial u}{\partial y}+2 v \frac{\partial v}{\partial y} .
\end{array}\right.
$$
Plug in the Cauchy-Riemann equations and we get
$$
\begin{gathered}
u \frac{\partial v}{\partial y}+v \frac{\partial v}{\partial x}=0 \\
-u \frac{\partial v}{\partial x}+v \frac{\partial v}{\partial y}=0 \\
(1.14) \Rightarrow \frac{\partial v}{\partial x}=\frac{v}{u} \frac{\partial v}{\partial y}
\end{gathered}
$$
Plug (1.15) into (1.13) and we get
$$
\frac{u^2+v^2}{u} \frac{\partial v}{\partial y}=0 .
$$
So $u^2+v^2=0$ or $\frac{\partial v}{\partial y}=0$.

If $u^2+v^2=0$, then, since $u, v$ are real, $u=v=0$, and thus $f=0$ which is constant.

Thus we may assume $u^2+v^2$ equals a non-zero constant, and we may divide by it. We multiply both sides by $u$ and find $\frac{\partial v}{\partial y}=0$, then by (1.15), $\frac{\partial v}{\partial x}=0$, and by Cauchy-Riemann, $\frac{\partial u}{\partial x}=0$.
$$
f^{\prime}=\frac{\partial f}{\partial x}=\frac{\partial u}{\partial x}+i \frac{\partial v}{\partial x}=0 .
$$
Thus $f$ is constant.
Why is the above only mostly a proof? The problem is we have a division by $u$, and need to make sure everything is well-defined. Specifically, we need to know that $u$ is never zero. We do have $f^{\prime}=0$ except at points where $u=0$, but we would need to investigate that a bit more.
Let's return to
$$
\left\{\begin{array}{l}
0=\frac{\partial\left(u^2+v^2\right)}{\partial x}=2 u \frac{\partial u}{\partial x}+2 v \frac{\partial v}{\partial x} . \\
0=\frac{\partial\left(u^2+v^2\right)}{\partial y}=2 u \frac{\partial u}{\partial y}+2 v \frac{\partial v}{\partial y} .
\end{array}\right.
$$
Plug in the Cauchy-Riemann equations and we get
$$
\begin{array}{r}
u \frac{\partial v}{\partial y}+v \frac{\partial v}{\partial x}=0 \\
-u \frac{\partial v}{\partial x}+v \frac{\partial v}{\partial y}=0 .
\end{array}
$$
We multiply the first equation $u$ and the second by $v$, and obtain
$$
\begin{aligned}
u^2 \frac{\partial v}{\partial y}+u v \frac{\partial v}{\partial x} & =0 \\
-u v \frac{\partial v}{\partial x}+v^2 \frac{\partial v}{\partial y} & =0 .
\end{aligned}
$$
Adding the two yields
$$
u^2 \frac{\partial v}{\partial y}+v^2 \frac{\partial v}{\partial y}=0,
$$
or equivalently
$$
\left(u^2+v^2\right) \frac{\partial v}{\partial y}=0 .
$$
We now argue in a similar manner as before, except now we don't have the annoying $u$ in the denominator. If $u^2+v^2=0$ then $u=v=0$, else we can divide by $u^2+v^2$ and find $\partial v / \partial y=0$. Arguing along these lines finishes the proof.
-/

theorem Shakarchi_exercise_1_13c {f : ℂ → ℂ} (Ω : Set ℂ) (a b : Ω) (h : IsOpen Ω)
  (hf : DifferentiableOn ℂ f Ω) (hc : ∃ (c : ℝ), ∀ z ∈ Ω, ‖f z‖ = c) :
  f a = f b := by
  sorry

/-
The statement above is false as written: the open set `Ω` is not assumed to be connected,
so the function can be constant (hence holomorphic) on each connected component but take
different values on different components; the norm will still be constant if those values
lie on the same circle.  The proof below formalizes this example.
-/

theorem Shakarchi_exercise_1_13c_neg :
    ¬ (∀ (Ω : Set ℂ), ∀ (f : ℂ → ℂ), ∀ (a b : Ω),
        IsOpen Ω → DifferentiableOn ℂ f Ω →
        (∃ c : ℝ, ∀ z ∈ Ω, ‖f z‖ = c) → f a = f b) := by
  -- Step 1: Assume toward contradiction that the universally quantified claim holds.
  intro h
  -- Step 2: Define the two open half-planes whose union is a disconnected open set Ω.
  let leftHalf : Set ℂ := {z : ℂ | z.re < 0}
  let rightHalf : Set ℂ := {z : ℂ | 0 < z.re}
  let Ω : Set ℂ := leftHalf ∪ rightHalf
  -- Step 3: Record that each half-plane is open, hence their union Ω is open.
  have h_left_open : IsOpen leftHalf :=
    isOpen_lt continuous_re continuous_const
  have h_right_open : IsOpen rightHalf :=
    isOpen_lt continuous_const continuous_re
  have hΩ : IsOpen Ω := h_left_open.union h_right_open
  -- Step 4: Define a holomorphic function that is constant on each component but flips sign.
  let f : ℂ → ℂ := fun z => if z.re < 0 then (1 : ℂ) else (-1 : ℂ)
  -- Step 5: Show differentiability of f on the left half-plane by comparing with a constant map.
  have h_left_diff :
      DifferentiableOn ℂ f leftHalf := by
    -- Step 5.1: On the left half-plane the function is literally the constant 1.
    have hconst :
        DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) leftHalf := by
      simp [differentiableOn_const]
    exact hconst.congr <| by
      intro z hz
      have hz' : z.re < 0 := hz
      simp [f, hz']
  -- Step 6: Show differentiability of f on the right half-plane via the constant (-1).
  have h_right_diff :
      DifferentiableOn ℂ f rightHalf := by
    -- Step 6.1: On the right half-plane the defining `if`-expression always chooses -1.
    have hconst :
        DifferentiableOn ℂ (fun _ : ℂ => (-1 : ℂ)) rightHalf := by
      simp [differentiableOn_const]
    exact hconst.congr <| by
      intro z hz
      have hzpos : 0 < z.re := hz
      have hz' : ¬ z.re < 0 := not_lt.mpr (le_of_lt hzpos)
      simp [f, hz']
  -- Step 7: Combine the two pieces to obtain differentiability on all of Ω.
  have hf : DifferentiableOn ℂ f Ω :=
    DifferentiableOn.union_of_isOpen h_left_diff h_right_diff h_left_open h_right_open
  -- Step 8: The norm of f is constantly 1 on Ω because both 1 and -1 have norm 1.
  have hc : ∃ c : ℝ, ∀ z ∈ Ω, ‖f z‖ = c := by
    refine ⟨1, ?_⟩
    intro z hz
    -- Step 8.1: Examine which half-plane z belongs to and simplify.
    rcases hz with hz | hz
    ·
      have hz' : z.re < 0 := hz
      simp [f, hz']
    ·
      have hzpos : 0 < z.re := hz
      have hz' : ¬ z.re < 0 := not_lt.mpr (le_of_lt hzpos)
      simp [f, hz']
  -- Step 9: Choose explicit subtype points a and b in different components of Ω.
  have ha_mem : ((-1 : ℂ) ∈ Ω) := Or.inl (by simp [leftHalf])
  have hb_mem : ((1 : ℂ) ∈ Ω) := Or.inr (by simp [rightHalf])
  let a : Ω := ⟨-1, ha_mem⟩
  let b : Ω := ⟨1, hb_mem⟩
  -- Step 10: Compute the values of f at the chosen points.
  have ha_val : f a = 1 := by
    -- Step 10.1: (a : ℂ) lies in the left half-plane by construction.
    simp [f, a]
  have hb_val : f b = -1 := by
    -- Step 10.2: (b : ℂ) lies in the right half-plane by construction.
    simp [f, b]
  have hne : f a ≠ f b := by
    -- Step 10.3: Evaluate numerically to finish the contradiction.
    have hRe : (1 : ℝ) ≠ (-1 : ℝ) := by
      norm_num
    intro h
    apply hRe
    have := congrArg Complex.re h
    simpa [ha_val, hb_val] using this
  -- Step 11: Apply the assumed universal claim to this specific data and reach a contradiction.
  exact hne (h Ω f a b hΩ hf hc)

/-
Corrected version: adding the hypothesis that Ω is preconnected forces the two points to lie
in the same connected component, so the classical maximum modulus principle applies and
shows that f is constant.  The proof below formalizes this fix.
-/

theorem Shakarchi_exercise_1_13c_corrected {f : ℂ → ℂ} {Ω : Set ℂ} (a b : Ω)
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hf : DifferentiableOn ℂ f Ω) (hc : ∃ c : ℝ, ∀ z ∈ Ω, ‖f z‖ = c) :
    f a = f b := by
  -- Step 1: Extract the constant value of ‖f z‖ from the hypothesis.
  obtain ⟨c, hc⟩ := hc
  -- Step 2: Package the maximality of the norm at the point a.
  have hmax : IsMaxOn (fun z => ‖f z‖) Ω a := by
    -- Step 2.1: Every point of Ω has the same norm, hence no one can exceed the value at a.
    intro z hz
    simp [hc z hz, hc a a.property]
  -- Step 3: Apply the maximum modulus principle on preconnected sets.
  have hEq :
      Set.EqOn f (fun _ => f a) Ω :=
    eqOn_of_isPreconnected_of_isMaxOn_norm hconn hΩ hf a.property hmax
  -- Step 4: Evaluate this equality-on-set statement at the point b.
  have hb_mem : ((b : ℂ) ∈ Ω) := b.property
  have hb := hEq hb_mem
  -- Step 5: The previous step already states f b = f a; rewrite to match the goal.
  simp [hb]
