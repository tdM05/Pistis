import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $(X, d_X)$ and $(Y, d_Y)$ be metric spaces; let $Y$ be complete. Let $A \subset X$. Show that if $f \colon A \rightarrow Y$ is uniformly continuous, then $f$ can be uniquely extended to a continuous function $g \colon \bar{A} \rightarrow Y$, and $g$ is uniformly continuous.
-/

/-Informal Proof

Let $\left(X, d_X\right)$ and $\left(Y, d_Y\right)$ be metric spaces; let $Y$ be complete. Let $A \subset X$. It is also given that $f: A \longrightarrow X$ is a uniformly continuous function. Then we have to show that $f$ can be uniquely extended to a continuous function $g: \bar{A} \longrightarrow Y$, and $g$ is uniformly continuous.
We define the function $g$ as follows:
$$
g(x)= \begin{cases}f(x) & \text { if } x \in A \\ \lim _{n \rightarrow \infty} f\left(x_n\right) & \text { if } x \in \bar{A},\end{cases}
$$
where $\left\{x_n\right\} \subset A$ is some sequence in $A$ such that $\lim _{n \rightarrow \infty} x_n=x$. Now we have to check that the above definition is well defined. We first note that since $\left\{x_n\right\} \subset A$ is convergent in $X,\left\{x_n\right\}$ is Cauchy in $A$ and since $f$ is uniformly continuous on $A,\left\{f\left(x_n\right)\right\}$ is Cauchy in $Y$. Further, since $Y$ is complete $\left\{f\left(x_n\right)\right\}$ is convergent. So let us now consider two sequences $\left\{x_n\right\}$ and $\left\{y_n\right\}$ such that $\lim _{n \rightarrow \infty} x_n=\lim _{n \rightarrow \infty} y_n=x$. Then we need to prove that $\lim _{n \rightarrow \infty} f\left(x_n\right)=\lim _{n \rightarrow \infty} f\left(y_n\right)=f(x)$. Let
$$
\lim _{n \rightarrow \infty} f\left(x_n\right)=a \text { and } b=\lim _{n \rightarrow \infty} f\left(y_n\right)
$$
Now since $f$ is uniformly continuous for any given $\epsilon>0$ there exists $\delta>0$ such that
$$
d_Y(f(x), f(y))<\epsilon \text { whenever } d_X(x, y)<\delta \text { and } x, y \in A
$$
So for this $\delta>0$ there exists $N \in \mathbb{N}$ such that
$$
d_X\left(x_n, x\right)<\frac{\delta}{2} \text { and } d_X\left(y_n, x\right)<\frac{\delta}{2}, \text { foe all } n \geq N .
$$
Therefore, we have that for all $n \geq N$,
$$
d_X\left(x_n, y_n\right)<\delta
$$
Thus the equation (1) yields us that
$$
d_Y\left(f\left(x_n\right), f\left(y_n\right)\right)<\epsilon \text { for all } n \geq N .
$$
Now since $\lim _{n \rightarrow \infty} f\left(x_n\right)=a$ and $b=\lim _{n \rightarrow \infty} f\left(y_n\right)$, so for the above $\epsilon>0$ we have a natural number $K \geq N$ such that
$$
\begin{gathered}
d_Y\left(f\left(x_n\right), a\right)<\epsilon \text { for all } n \geq K \text { and } \\
d_Y\left(f\left(y_n\right), b\right)<\epsilon \text { for all } n \geq K .
\end{gathered}
$$
Moreover, since $K \geq N$, from $(2)$ we get
$$
d_Y\left(f\left(x_n\right), f\left(y_n\right)\right)<\epsilon \text { for all } n \geq K .
$$
Now we calculate the following, for $n \geq K$,
$$
\begin{array}{rlr}
d_Y(a, b) & \leq & d_Y\left(a, f\left(x_n\right)\right)+d_Y\left(f\left(x_n\right), f\left(y_n\right)\right)+d\left(f\left(y_n\right), b\right) \\
& < & \epsilon+\epsilon+\epsilon \text { by }(3),(4) \text { and }(5) \\
& = & 3 \epsilon
\end{array}
$$
where the first inequality holds because of triangular inequality. Since $\epsilon>0$ is arbitrary the above calculation shows that $d_Y(a, b)=0$. Thus, the above definition is independent of the choice of the sequence $\left\{x_n\right\}$ and hence the map $g$ is well defined. Moreover, from the construction it follows that $g$ is continuous on $\bar{A}$.
Moreover, we observe that $g$ is unique extension of $f$ by the construction.
So it remains to show that $g$ is uniformly continuous. In order to that we take a Cauchy sequence $\left\{a_n\right\} \subset \bar{A}$. Then since $\bar{A}$ is a closed set so the sequence $\left\{a_n\right\}$ is convergent and hence $\left\{g\left(a_n\right)\right\}$ is also a convergent sequence as $g$ is continuous on $\bar{A}$. So $\left\{g\left(a_n\right)\right\}$ is a Cauchy sequence in $Y$. Since a function is uniformly continuous if and only if it sends Cauchy sequences to Cauchy sequences, we conclude that $g$ is uniformly continuous.
-/

theorem Munkres_exercise_43_2 {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (A : Set X)
  (f : X → Y) (hf : UniformContinuousOn f A) :
  ∃! (g : X → Y), ContinuousOn g (closure A) ∧
  UniformContinuousOn g (closure A) ∧ ∀ (x : A), g x = f x := by
  sorry

/-
The universal statement above is false as written: taking `X = ℝ`, `Y = ℝ`,
`A = ∅`, and any uniformly continuous `f`, *every* function `g : ℝ → ℝ`
vacuously satisfies the hypotheses on `closure A = ∅`, so uniqueness fails.
-/

theorem Munkres_exercise_43_2_neg :
    ∃ (X : Type*) (_ : MetricSpace X) (Y : Type*) (_ : MetricSpace Y) (_ : CompleteSpace Y)
        (A : Set X) (f : X → Y),
        UniformContinuousOn f A ∧
          ¬ ∃! (g : X → Y),
            ContinuousOn g (closure A) ∧
              UniformContinuousOn g (closure A) ∧ ∀ x : A, g x = f x := by
  classical
  -- Step 1: Exhibit concrete data (`X = ULift ℝ`, `Y = ℝ`, `A = ∅`, `f = 0`) for the counterexample.
  -- Step 2: Fix `X = ℝ`, `Y = ℝ`, `A = ∅`, and let `f` be the zero function (which is uniformly continuous).
  let X := ULift ℝ
  let Y := ULift ℝ
  let f : X → Y := fun _ => ⟨0⟩
  have hf :
      UniformContinuousOn f (∅ : Set X) := by
    -- Step 2.0: A constant function is uniformly continuous on every subset via restriction.
    refine (uniformContinuousOn_iff_restrict).2 ?_
    have hf_uc : UniformContinuous f := uniformContinuous_const
    exact hf_uc.comp
      (uniformContinuous_subtype_val :
        UniformContinuous (Subtype.val : (∅ : Set X) → X))
  -- Step 4: Build two distinct global functions that both satisfy the required property on `closure ∅ = ∅`.
  let g0 : X → Y := fun _ => ⟨0⟩
  let g1 : X → Y := fun _ => ⟨1⟩
  have hg0 :
      ContinuousOn g0 (closure (∅ : Set X)) ∧
        UniformContinuousOn g0 (closure (∅ : Set X)) ∧
          ∀ x : (∅ : Set X), g0 x = f x := by
    -- Step 4.1: Any constant function is continuous and uniformly continuous everywhere.
    refine
      ⟨(continuous_const : Continuous g0).continuousOn,
        (uniformContinuousOn_iff_restrict).2
          ((uniformContinuous_const : UniformContinuous g0).comp
            (uniformContinuous_subtype_val :
              UniformContinuous (Subtype.val : closure (∅ : Set X) → X))),
        ?_⟩
    -- Step 4.2: The equality on `(∅ : Set ℝ)` is vacuous.
    intro x
    cases x.property
  have hg1 :
      ContinuousOn g1 (closure (∅ : Set X)) ∧
        UniformContinuousOn g1 (closure (∅ : Set X)) ∧
          ∀ x : (∅ : Set X), g1 x = f x := by
    -- Step 4.3: Repeat the same reasoning for the constant-one function.
    refine
      ⟨(continuous_const : Continuous g1).continuousOn,
        (uniformContinuousOn_iff_restrict).2
          ((uniformContinuous_const : UniformContinuous g1).comp
            (uniformContinuous_subtype_val :
              UniformContinuous (Subtype.val : closure (∅ : Set X) → X))),
        ?_⟩
    -- Step 4.4: Again, the equality on the empty subtype holds trivially.
    intro x
    cases x.property
  -- Step 5: Show the supposed uniqueness fails for these concrete data.
  refine ⟨X, inferInstance, Y, inferInstance, inferInstance, (∅ : Set X), f, hf, ?_⟩
  -- Step 5.1: If uniqueness held, we would derive `g0 = g1`, contradicting their distinct values.
  intro hUnique
  rcases hUnique with ⟨g, hg, huniq⟩
  have h0 : g0 = g := huniq g0 hg0
  have h1 : g1 = g := huniq g1 hg1
  have hEq : g0 = g1 := h0.trans h1.symm
  have hcongr := congrArg (fun h : X → Y => h ⟨0⟩) hEq
  have : False := by
    have hdown : (0 : ℝ) = 1 := by
      simpa [g0, g1] using congrArg ULift.down hcongr
    have : (0 : ℝ) ≠ 1 := by simp
    exact this hdown
  exact this

/-
Corrected version:

The previous `_corrected` formulation used `∃! g, Continuous g ∧ UniformContinuous g ∧ ext g`,
which only asserts uniqueness among continuous *and* uniformly continuous extensions. The
informal statement (Munkres Exercise 43.2) asserts two things separately:
  (1) f extends **uniquely** to a continuous function g : Ā → Y (unique among ALL continuous
      extensions, not just uniformly continuous ones), and
  (2) this unique extension g is in fact uniformly continuous.

Although in this setting (metric spaces, Y complete, A dense in Ā) the two are equivalent
(any two continuous extensions agreeing on a dense subset of a Hausdorff space must agree
everywhere), the faithful formalization should separate the concerns to match the informal
structure: assert existence of a UC extension, then assert uniqueness among all continuous
extensions.
-/

theorem Munkres_exercise_43_2_corrected {X : Type*} [MetricSpace X]
    {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (A : Set X)
    (f : X → Y) (hf : UniformContinuousOn f A) :
    ∃ (g : closure A → Y),
      UniformContinuous g ∧
        (∀ x : A, g ⟨x, subset_closure x.property⟩ = f x) ∧
        (∀ g' : closure A → Y, Continuous g' →
          (∀ x : A, g' ⟨x, subset_closure x.property⟩ = f x) → g' = g) := by
  classical
  -- Step 1: Identify the dense subset `s` of `closure A` consisting of points that lie in `A`.
  set sSet : Set (closure A) := {x | (x : X) ∈ A} with hsDef
  -- Step 1.1: characterize membership in `sSet`.
  have hs_mem : ∀ {x : closure A}, x ∈ sSet ↔ (x : X) ∈ A := by
    intro x; simp [hsDef]
  -- Step 1.2: prove `sSet` is dense in `closure A`.
  have hs_dense : Dense sSet := by
    refine dense_iff_closure_eq.mpr ?_
    ext x
    constructor
    · intro _; trivial
    · intro _
      refine Metric.mem_closure_iff.2 ?_
      intro ε hε
      -- Step 1.2.1: because `(x : X) ∈ closure A`, approximate it by a point of `A`.
      have hx' : ((x : X) ∈ closure A) := x.property
      obtain ⟨z, hzA, hzDist⟩ := Metric.mem_closure_iff.1 hx' ε hε
      -- Step 1.2.2: promote `z` to a point of `closure A` that still lies in `A`.
      let y : closure A := ⟨z, subset_closure hzA⟩
      have hy : y ∈ sSet := (hs_mem (x := y)).2 hzA
      -- Step 1.2.3: distances in the subtype agree with those in `X`.
      have hzDist' : dist ((x : X)) z < ε := by simpa [dist_comm] using hzDist
      have hdist : dist x y < ε := by simpa [y] using hzDist'
      exact ⟨y, hy, hdist⟩
  -- Step 2: Package the restriction of `f` to `A` as a uniformly continuous map on `s`.
  -- Step 2.1: rewrite the assumption using the restriction characterization.
  have hf_restrict : UniformContinuous (A.restrict f) := by
    simpa using (uniformContinuousOn_iff_restrict.mp hf)
  -- Step 2.2: define the canonical map from `s` to `A`.
  let toA : sSet → A := fun x => ⟨(x : X), (hs_mem (x := x)).1 x.property⟩
  -- Step 2.3: prove that `toA` is uniformly continuous (induced by inclusions).
  have h_toA_uc : UniformContinuous toA := by
    have h_coe :
        UniformContinuous fun x : sSet => ((x : closure A) : X) :=
          (uniformContinuous_subtype_val :
              UniformContinuous ((Subtype.val : closure A → X))).comp
            (uniformContinuous_subtype_val :
              UniformContinuous (Subtype.val : sSet → closure A))
    exact (UniformContinuous.subtype_mk h_coe fun x => (hs_mem (x := x)).1 x.property)
  -- Step 2.4: combine to obtain a uniformly continuous map on `s`.
  have hf_s :
      UniformContinuous fun x : sSet => f ((x : closure A) : X) :=
        hf_restrict.comp h_toA_uc
  -- Step 3: Extend the restricted map from the dense subset `s` to all of `closure A`.
  let g : closure A → Y := hs_dense.extend fun x : sSet => f ((x : closure A) : X)
  -- Step 3.1: the extension is uniformly continuous by Mathlib's `Dense.uniformContinuous_extend`.
  have hg_uc : UniformContinuous g := hs_dense.uniformContinuous_extend hf_s
  -- Step 4: Show that the extension agrees with `f` on `A`.
  have hg_agree : ∀ x : A, g ⟨x, subset_closure x.property⟩ = f x := by
    intro x
    -- Step 4.1: view `x` as a point of the dense subset `s`.
    let sx : sSet :=
      ⟨⟨x, subset_closure x.property⟩,
        (hs_mem (x := ⟨x, subset_closure x.property⟩)).2 x.property⟩
    -- Step 4.2: apply the extension specification on dense points.
    simpa using hs_dense.extend_of_ind hf_s sx
  -- Step 5: Prove uniqueness among ALL continuous extensions (not just UC ones).
  have hg_unique : ∀ g' : closure A → Y, Continuous g' →
      (∀ x : A, g' ⟨x, subset_closure x.property⟩ = f x) → g' = g := by
    intro g' hg'_cont hg'_agree
    -- Step 5.1: show `g'` and `g` coincide on the dense subset `s`.
    have h_on_s :
        g ∘ (Subtype.val : sSet → closure A) =
          g' ∘ (Subtype.val : sSet → closure A) := by
      funext x
      -- Step 5.1.1: turn `x` into an element of `A`.
      let ax : A := ⟨(x : X), (hs_mem (x := x)).1 x.property⟩
      -- Step 5.1.2: use both agreement hypotheses to show they give the same value.
      have hx_g : g ⟨ax, subset_closure ax.property⟩ = f ax := hg_agree ax
      have hx_g' : g' ⟨ax, subset_closure ax.property⟩ = f ax := hg'_agree ax
      simpa using hx_g.trans hx_g'.symm
    -- Step 5.2: since `sSet` is dense, two continuous functions agreeing on it must be equal.
    have hDenseRange : DenseRange (Subtype.val : sSet → closure A) :=
      hs_dense.denseRange_val
    -- Step 5.3: apply the density equalizer lemma (Hausdorff separation).
    exact (DenseRange.equalizer hDenseRange hg_uc.continuous hg'_cont h_on_s).symm
  -- Step 6: Package everything into the existential.
  exact ⟨g, hg_uc, hg_agree, hg_unique⟩
