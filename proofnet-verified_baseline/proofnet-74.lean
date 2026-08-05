import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

If $G$ is a group and $a, x \in G$, prove that $C\left(x^{-1} a x\right)=x^{-1} C(a) x$
-/

/-Informal Proof

Note that
$$
C(a):=\{x \in G \mid x a=a x\} .
$$
Let us assume $p \in C\left(x^{-1} a x\right)$. Then,
$$
\begin{aligned}
& p\left(x^{-1} a x\right)=\left(x^{-1} a x\right) p \\
\Longrightarrow & \left(p x^{-1} a\right) x=x^{-1}(a x p) \\
\Longrightarrow & x\left(p x^{-1} a\right)=(a x p) x^{-1} \\
\Longrightarrow & \left(x p x^{-1}\right) a=a\left(x p x^{-1}\right) \\
\Longrightarrow & x p x^{-1} \in C(a) .
\end{aligned}
$$
Therefore,
$$
p \in C\left(x^{-1} a x\right) \Longrightarrow x p x^{-1} \in C(a) .
$$
Thus,
$$
C\left(x^{-1} a x\right) \subset x^{-1} C(a) x .
$$
Let us assume
$$
q \in x^{-1} C(a) x .
$$
Then there exists an element $y$ in $C(a)$ such that
$$
q=x^{-1} y x
$$
Now,
$$
y \in C(a) \Longrightarrow y a=a y .
$$
Also,
$$
q\left(x^{-1} a x\right)=\left(x^{-1} y x\right)\left(x^{-1} a x\right)=x^{-1}(y a) x=x^{-1}(y a) x=\left(x^{-1} y x\right)\left(x^{-1} a x\right)=\left(x^{-1} y x\right) q .
$$
Therefore,
$$
q\left(x^{-1} a x\right)=\left(x^{-1} y x\right) q
$$
So,
$$
q \in C\left(x^{-1} a x\right) .
$$
Consequently we have
$$
x^{-1} C(a) x \subset C\left(x^{-1} a x\right) .
$$
It follows from the aforesaid argument
$$
C\left(x^{-1} a x\right)=x^{-1} C(a) x .
$$
This completes the proof.
-/

theorem Herstein_exercise_2_3_17 {G : Type*} [Mul G] [Group G] (a x : G) :
  centralizer {x⁻¹*a*x} =
  (λ g : G => x⁻¹*g*x) '' (centralizer {a}) := by
  sorry

/-
Step-by-step note on the failed proof attempt:
* The statement quantifies over an arbitrary multiplication `Mul G` **independent** from the
  group structure `[Group G]`. The group operations (including `⁻¹`) come from `[Group G]`,
  while the centralizers and conjugations in the statement are built using the *separate*
  `Mul` instance. Without a coherence assumption these two structures can disagree, so the
  equality is not provable in general. Below we exhibit an explicit counterexample and then
  give the corrected version of the theorem assuming only `[Group G]`, which matches the
  intended mathematical statement.
-/

/-- An alternate multiplication on `Multiplicative Bool`: it is the constant function returning
`false`, so every product collapses to the absorbing element.  Kept as a plain definition so it
can be supplied explicitly as the `[Mul]` witness in the counterexample. -/
def mulBoolAnd : Mul (Multiplicative Bool) :=
  ⟨fun _ _ => Multiplicative.ofAdd false⟩

/--
Negation of the original statement: there exist a type, a multiplication, a group structure,
and elements `a x` for which the displayed equality of centralizers fails.  We use `Bool`
with `Mul` = conjunction and `Group` = xor. Detailed steps below. -/
theorem Herstein_exercise_2_3_17_neg :
  ∃ (G : Type) (_m : Mul G) (_grp : Group G) (a x : G),
    centralizer {x⁻¹ * a * x} ≠ (fun g : G => x⁻¹ * g * x) '' (centralizer {a}) := by
  -- Step 1: Choose the specific ambient data (type and instances).
  refine ⟨Multiplicative Bool, mulBoolAnd, (inferInstance : Group (Multiplicative Bool)),
    Multiplicative.ofAdd true, Multiplicative.ofAdd false, ?_⟩
  -- Introduce the chosen structures as local instances so that `*` and `⁻¹` use them.
  let _ : Mul (Multiplicative Bool) := mulBoolAnd
  -- Step 2: Compute the two sets in the statement for `a = true`, `x = false`.
  -- 2.1 Left side: centralizer of `{false⁻¹ * true * false}`; with the chosen operations this
  --     element is `false`.
  have h_left_mem : Multiplicative.ofAdd true ∈ centralizer ({Multiplicative.ofAdd false} : Set (Multiplicative Bool)) := by
    -- Step 2.1.1: To show membership, verify commutation with the sole element `false`.
    intro b hb
    -- `b` must be `false` because the set is a singleton, and every product is `false` anyway.
    have hb' : b = Multiplicative.ofAdd false := by simpa using hb
    subst hb'
    rfl
  -- 2.2 Right side: image of the map `g ↦ false * g * false`. With conjunction, this map
  --     is constantly `false`, so its image is `{false}` and hence cannot contain `true`.
  have h_right_not : Multiplicative.ofAdd true ∉
      (fun g : Multiplicative Bool => (Multiplicative.ofAdd false) * g * (Multiplicative.ofAdd false)) ''
      (centralizer ({Multiplicative.ofAdd true} : Set (Multiplicative Bool))) := by
    intro h
    rcases h with ⟨g, -, hg⟩
    -- Evaluate the map: `false * g * false` simplifies to `false` for any `g`.
    have hconst : (Multiplicative.ofAdd false) * g * (Multiplicative.ofAdd false) =
        (Multiplicative.ofAdd false : Multiplicative Bool) := by
      rfl
    -- The equation `hg` claims this constant is `true`, contradiction.
    have : (Multiplicative.ofAdd false : Multiplicative Bool) = Multiplicative.ofAdd true := by
      simp [hconst] at hg
    cases this
  -- Step 3: Conclude the two sets differ because `true` belongs to the left but not the right.
  intro hEq
  -- transport membership across the assumed equality of sets
  have hInLeft : Multiplicative.ofAdd true ∈ centralizer
      ({(Multiplicative.ofAdd false)⁻¹ * Multiplicative.ofAdd true * Multiplicative.ofAdd false} : Set (Multiplicative Bool)) := by
    -- the element inside the singleton is `ofAdd false`, so reuse `h_left_mem`
    simpa using h_left_mem
  have hInRight : Multiplicative.ofAdd true ∈
      (fun g : Multiplicative Bool => (Multiplicative.ofAdd false)⁻¹ * g * (Multiplicative.ofAdd false)) ''
      (centralizer ({Multiplicative.ofAdd true} : Set (Multiplicative Bool))) := by
    simpa [hEq] using hInLeft
  exact h_right_not hInRight

/--
Corrected version: when the multiplication is the one coming from the group structure (i.e. we
only assume `[Group G]`), the expected equality of centralizers holds. Detailed annotated proof
is given below. -/
theorem Herstein_exercise_2_3_17_corrected {G : Type*} [Group G] (a x : G) :
  centralizer {x⁻¹ * a * x} = (fun g : G => x⁻¹ * g * x) '' (centralizer {a}) := by
  -- Step 1: Use set extensionality to prove equality by mutual inclusion.
  ext g
  constructor
  · -- Step 2: Forward inclusion. Assume `g` centralizes `x⁻¹ * a * x`.
    intro hg
    -- Step 2.1: Define `y = x * g * x⁻¹`; then `g = x⁻¹ * y * x`.
    refine ⟨x * g * x⁻¹, ?_, ?_⟩
    · -- Step 2.1.1: Show `y` commutes with `a`, so `y ∈ centralizer {a}`.
      have hcomm : (x⁻¹ * a * x) * g = g * (x⁻¹ * a * x) := by
        -- Extract commutation from `hg` using the unique element of the singleton.
        have := hg (x⁻¹ * a * x) (by simp)
        simpa using this
      -- Conjugate the equality by multiplying with `x` on the left and `x⁻¹` on the right.
      have hcomm' : a * (x * g * x⁻¹) = (x * g * x⁻¹) * a := by
        calc
          a * (x * g * x⁻¹)
              = x * ((x⁻¹ * a * x) * g) * x⁻¹ := by simp [mul_assoc]
          _ = x * (g * (x⁻¹ * a * x)) * x⁻¹ := by
                simpa using congrArg (fun z => x * z * x⁻¹) hcomm
          _ = (x * g * x⁻¹) * a := by simp [mul_assoc]
      -- Package the commutation into the centralizer predicate.
      intro b hb
      have hb' : b = a := by simpa using hb
      subst hb'
      simpa using hcomm'
    · -- Step 2.2: Verify `x⁻¹ * y * x = g` for `y = x * g * x⁻¹`.
      simp [mul_assoc]
  · -- Step 3: Reverse inclusion. Start with `g` in the image, write `g = x⁻¹ * y * x`.
    intro hg
    rcases hg with ⟨y, hy, rfl⟩
    -- Step 3.1: From `y ∈ centralizer {a}` get `a * y = y * a`.
    have hya : a * y = y * a := by
      have := hy a (by simp)
      simpa using this
    -- Step 3.2: Show `x⁻¹ * y * x` commutes with `x⁻¹ * a * x`.
    intro b hb
    have hb' : b = x⁻¹ * a * x := by simpa using hb
    subst hb'
    calc
      (x⁻¹ * a * x) * (x⁻¹ * y * x)
          = x⁻¹ * a * x * x⁻¹ * y * x := by simp [mul_assoc]
      _ = x⁻¹ * a * y * x := by simp [mul_assoc]
      _ = x⁻¹ * y * a * x := by simp [hya, mul_assoc]
      _ = x⁻¹ * y * x * x⁻¹ * a * x := by simp [mul_assoc]
      _ = (x⁻¹ * y * x) * (x⁻¹ * a * x) := by simp [mul_assoc]
