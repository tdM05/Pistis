import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that $(x, y)$ is not a principal ideal in $\mathbb{Q}[x, y]$.
-/

/-Informal Proof

Suppose, to the contrary, that $(x, y)=p$ for some polynomial $p \in \mathbb{Q}[x, y]$. From $x, y \in$ $(x, y)=(p)$ there are $s, t \in \mathbb{Q}[x, y]$ such that $x=s p$ and $y=t p$.
Then:
$$
\begin{aligned}
& 0=\operatorname{deg}_y(x)=\operatorname{deg}_y(s)+\operatorname{deg}_y(p) \text { so } \\
& 0=\operatorname{deg}_y(p) \\
& 0=\operatorname{deg}_x(y)=\operatorname{deg}_x(s)+\operatorname{deg}_x(p) \text { so } \\
& 0=\operatorname{deg}_x(p) \text { so }
\end{aligned}
$$
From : $\quad 0=\operatorname{deg}_y(p)=\operatorname{deg}_x(p)$ we get $\operatorname{deg}(p)=0$ and $p \in \mathbb{Q}$.
But $p \in(p)=(x, y)$ so $p=a x+b y$ for some $a, b \in \mathbb{Q}[x, y]$
$$
\begin{aligned}
\operatorname{deg}(p) & =\operatorname{deg}(a x+b y) \\
& =\min (\operatorname{deg}(a)+\operatorname{deg}(x), \operatorname{deg}(b)+\operatorname{deg}(y)) \\
& =\min (\operatorname{deg}(a)+1, \operatorname{deg}(b)+1) \geqslant 1
\end{aligned}
$$
which contradicts $\operatorname{deg}(p)=0$.
So we conclude that $(x, y)$ is not principal ideal in $\mathbb{Q}[x, y]$
-/

noncomputable section

theorem Dummit_Foote_exercise_9_1_6 : ¬ Submodule.IsPrincipal
  (span ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) ℚ))) := by
  -- Step 1: switch to classical logic so that we may freely extract witnesses from existential hypotheses.
  classical
  -- Step 2: assume towards a contradiction that the ideal is principal and obtain a generator g.
  intro hPrincipal
  obtain ⟨g, hgSpan⟩ := (Submodule.isPrincipal_iff _).1 hPrincipal
  -- Step 3: record that each variable lies in the original span and move those facts to the principal span of g.
  have hx0_mem :
      MvPolynomial.X (0 : Fin 2) ∈
        span ({MvPolynomial.X 0, MvPolynomial.X 1} :
          Set (MvPolynomial (Fin 2) ℚ)) :=
    Submodule.subset_span (by simp)
  have hx1_mem :
      MvPolynomial.X (1 : Fin 2) ∈
        span ({MvPolynomial.X 0, MvPolynomial.X 1} :
          Set (MvPolynomial (Fin 2) ℚ)) :=
    Submodule.subset_span (by simp)
  have hx0_mem_singleton :
      MvPolynomial.X (0 : Fin 2) ∈
          Submodule.span (MvPolynomial (Fin 2) ℚ) ({g} : Set _) := by
    simpa [hgSpan] using hx0_mem
  have hx1_mem_singleton :
      MvPolynomial.X (1 : Fin 2) ∈
          Submodule.span (MvPolynomial (Fin 2) ℚ) ({g} : Set _) := by
    simpa [hgSpan] using hx1_mem
  -- Step 4: unwrap the membership statements as explicit factorizations by the generator g.
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hx0_mem_singleton
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hx1_mem_singleton
  have ha_mul :
      a * g = MvPolynomial.X (0 : Fin 2) := by
    simpa using ha
  have hb_mul :
      b * g = MvPolynomial.X (1 : Fin 2) := by
    simpa using hb
  -- Step 5: pass the relations through the standard algebra equivalence φ isolating the second variable as a polynomial variable.
  let φ := MvPolynomial.finSuccEquiv ℚ 1
  have hφ_a :
      φ a * φ g = Polynomial.X := by
    simpa [map_mul, φ, MvPolynomial.finSuccEquiv_X_zero (R := ℚ) (n := 1)]
      using congrArg φ ha_mul
  have hφ_b' :
      φ b * φ g = Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    have hmap := congrArg φ hb_mul
    have hphiX :
        φ (MvPolynomial.X (1 : Fin 2)) =
          Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
      simpa [φ, Fin.succ_zero_eq_one]
        using
          (MvPolynomial.finSuccEquiv_X_succ (R := ℚ) (n := 1) (j := (0 : Fin 1)))
    simpa [map_mul, hphiX] using hmap
  have hφ_b :
      φ g * φ b = Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    simpa [mul_comm] using hφ_b'
  -- Step 6: use the primality of Polynomial.X to analyse the possible divisibilities.
  have hPrime :
      Prime (Polynomial.X : Polynomial (MvPolynomial (Fin 1) ℚ)) :=
    (Polynomial.irreducible_X).prime
  have hφ_a_comm :
      φ g * φ a = Polynomial.X := by
    simpa [mul_comm] using hφ_a
  have hdiv :
      (Polynomial.X : Polynomial (MvPolynomial (Fin 1) ℚ)) ∣ φ g * φ a := by
    refine ⟨1, ?_⟩
    simp [hφ_a_comm]
  -- Step 7: establish that Polynomial.X cannot divide the constant Polynomial.C (MvPolynomial.X 0).
  have hX_not_dvd :
      ¬ (Polynomial.X : Polynomial (MvPolynomial (Fin 1) ℚ)) ∣
          Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    intro h
    rcases h with ⟨q, hq⟩
    have hEval := congrArg (Polynomial.eval (0 : MvPolynomial (Fin 1) ℚ)) hq
    simp [MvPolynomial.X_ne_zero] at hEval
  have hcontr : False := by
    cases hPrime.dvd_or_dvd hdiv with
    | inl hdiv_g =>
      rcases hdiv_g with ⟨q, hq⟩
      have : (Polynomial.X : Polynomial (MvPolynomial (Fin 1) ℚ)) ∣
          Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
        have hEq :
            Polynomial.C (MvPolynomial.X (0 : Fin 1)) =
              Polynomial.X * (q * φ b) := by
          calc
            Polynomial.C (MvPolynomial.X (0 : Fin 1))
                = φ g * φ b := hφ_b.symm
            _ = (Polynomial.X * q) * φ b := by simp [hq]
            _ = Polynomial.X * (q * φ b) := by
              simp [mul_comm, mul_left_comm, mul_assoc]
        exact ⟨q * φ b, hEq⟩
      exact hX_not_dvd this
    | inr hdiv_a =>
      rcases hdiv_a with ⟨q, hq⟩
      have hcancel_eq :
          (Polynomial.X : Polynomial (MvPolynomial (Fin 1) ℚ)) * (φ g * q) =
            (Polynomial.X : Polynomial (MvPolynomial (Fin 1) ℚ)) * (1 : _) := by
        have hEq :
            (Polynomial.X : Polynomial (MvPolynomial (Fin 1) ℚ)) * (φ g * q) =
              Polynomial.X := by
          calc
            (Polynomial.X : _) * (φ g * q)
                = φ g * (Polynomial.X * q) := by
                  simp [mul_comm, mul_left_comm, mul_assoc]
            _ = Polynomial.X := by simpa [hq] using hφ_a_comm
        simpa [one_mul] using hEq
      have hcancel :
          φ g * q = (1 : Polynomial (MvPolynomial (Fin 1) ℚ)) :=
        mul_left_cancel₀ (Polynomial.X_ne_zero (R := MvPolynomial (Fin 1) ℚ)) hcancel_eq
      have hφg_unit :
          IsUnit (φ g) := by
        refine ⟨⟨φ g, q, hcancel, ?_⟩, rfl⟩
        simpa [mul_comm] using hcancel
      obtain ⟨u, hu⟩ := hφg_unit
      let u' := Units.map (φ.symm.toRingEquiv.toMonoidHom) u
      have hg_unit : IsUnit g := by
        refine ⟨u', ?_⟩
        have := congrArg φ.symm hu
        simpa using this
      have hOne_singleton :
          (1 : MvPolynomial (Fin 2) ℚ) ∈
            Submodule.span (MvPolynomial (Fin 2) ℚ) ({g} : Set _) := by
        rcases hg_unit with ⟨u0, hu0⟩
        refine Submodule.mem_span_singleton.mpr ?_
        refine ⟨(↑u0⁻¹ : MvPolynomial (Fin 2) ℚ), ?_⟩
        simp [hu0]
      have hOne_original :
          (1 : MvPolynomial (Fin 2) ℚ) ∈
            span ({MvPolynomial.X 0, MvPolynomial.X 1} :
              Set (MvPolynomial (Fin 2) ℚ)) := by
        simpa [hgSpan] using hOne_singleton
      have hproper :
          (1 : MvPolynomial (Fin 2) ℚ) ∉
            span ({MvPolynomial.X 0, MvPolynomial.X 1} :
              Set (MvPolynomial (Fin 2) ℚ)) := by
        intro h
        obtain ⟨c0, c1, hc⟩ := (Submodule.mem_span_pair).1 h
        have hEval := congrArg (MvPolynomial.eval fun _ => (0 : ℚ)) hc
        have : (0 : ℚ) = 1 := by simp at hEval
        exact one_ne_zero this.symm
      exact hproper hOne_original
  exact hcontr
