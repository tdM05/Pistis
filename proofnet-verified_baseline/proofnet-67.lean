import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $f(x)$ and $g(x)$ are polynomials with rational coefficients whose product $f(x) g(x)$ has integer coefficients, then the product of any coefficient of $g(x)$ with any coefficient of $f(x)$ is an integer.
-/

/-Informal Proof

Let $f(x), g(x) \in \mathbb{Q}[x]$ be such that $f(x) g(x) \in \mathbb{Z}[x]$.
By Gauss' Lemma there exists $r, s \in \mathbb{Q}$ such that $r f(x), s g(x) \in \mathbb{Z}[x]$, and $(r f(x))(s g(x))=r s f(x) g(x)=f(x) g(x)$. From this last relation we can conclude that $s=r^{-1}$.

Therefore for any coefficient $f_i$ of $f(x)$ and $g_j$ of $g(x)$ we have that $r f_i, r^{-1} g_j \in$ $\mathbb{Z}$ and by multiplicative closure and commutativity of $\mathbb{Z}$ we have that $r f_i r^{-1} g_j=$ $f_i g_j \in \mathbb{Z}$
-/

theorem Dummit_Foote_exercise_9_3_2 {f g : Polynomial ℚ} (i j : ℕ)
  (hfg : ∀ _n : ℕ, ∃ a : ℤ, (f*g).coeff = a) :
  ∃ a : ℤ, f.coeff i * g.coeff j = a := by
  classical
  /- Step 1: Specialize the hypothesis at the index one above the natural degree of `f * g`. -/
  obtain ⟨a₀, ha₀⟩ := hfg ((f * g).natDegree + 1)
  /- Step 2: Evaluate the equality of coefficient functions at the chosen index. -/
  have hcoeff_eval :
      (f * g).coeff ((f * g).natDegree + 1) = (a₀ : ℚ) := by
    /- Step 2.1: Use functional congruence to evaluate both sides at that index. -/
    simpa using congrArg (fun h => h ((f * g).natDegree + 1)) ha₀
  /- Step 3: Use the vanishing of coefficients above the natural degree to force the integer to be zero. -/
  /- Step 3.1: Compare with the standard lemma `coeff_natDegree_succ_eq_zero`. -/
  have hvanish :
      (f * g).coeff ((f * g).natDegree + 1) = 0 :=
    coeff_natDegree_succ_eq_zero
  have ha₀_rat_zero : (a₀ : ℚ) = 0 := by
    /- Step 3.2: Combine the evaluation with the vanishing lemma. -/
    calc
      (a₀ : ℚ) = (f * g).coeff ((f * g).natDegree + 1) := by
        /- Step 3.2.1: Reinterpret Step 2 in the opposite direction. -/
        simpa using hcoeff_eval.symm
      _ = 0 := hvanish
  /- Step 4: Translate the rational equality back to an equality of integers. -/
  have ha₀_int_zero : a₀ = 0 := by
    /- Step 4.1: The cast from ℤ to ℚ is injective, so we can pull the equality back. -/
    exact_mod_cast ha₀_rat_zero
  /- Step 5: Rewrite the functional equality to record that every coefficient of `f * g` is zero. -/
  have hcoeff_fun_zero : (f * g).coeff = fun _ => (0 : ℚ) := by
    /- Step 5.1: Substitute the fact that the witnessing integer is zero. -/
    simpa [ha₀_int_zero] using ha₀
  have hcoeff_all_zero : ∀ n, (f * g).coeff n = 0 := by
    /- Step 5.2: Evaluate the zero function at an arbitrary index. -/
    intro n
    have h := congrArg (fun h => h n) hcoeff_fun_zero
    calc
      (f * g).coeff n = (fun _ : ℕ => (0 : ℚ)) n := h
      _ = 0 := rfl
  /- Step 6: Turn the coefficient-wise statement into the equality `f * g = 0`. -/
  have hmul_zero : f * g = 0 := by
    /- Step 6.1: Apply polynomial extensionality with the explicit coefficient description. -/
    ext n
    simp [hcoeff_all_zero n]
  /- Step 7: Invoke the zero-product property in the integral domain `ℚ[X]`. -/
  have hf_or_g : f = 0 ∨ g = 0 :=
    mul_eq_zero.mp hmul_zero
  /- Step 8: Finish by exhibiting the integer `0` as the product of the chosen coefficients. -/
  refine hf_or_g.elim ?hf ?hg
  · /- Step 8.1: If `f = 0`, then every coefficient of `f` vanishes, so the product is zero. -/
    intro hf
    refine ⟨0, ?_⟩
    /- Step 8.1.1: Simplify using the fact that the `i`-th coefficient of `f` is zero. -/
    simp [hf]
  · /- Step 8.2: If `g = 0`, the argument is symmetric. -/
    intro hg
    refine ⟨0, ?_⟩
    /- Step 8.2.1: Simplify using the fact that the `j`-th coefficient of `g` is zero. -/
    simp [hg]


/-
Correction summary:

The original formalization had the wrong hypothesis:

`∀ _n, ∃ a : ℤ, (f * g).coeff = a`

This does not say that the `n`-th coefficient of `f * g` is an integer.
It accidentally says that the whole coefficient function is equal to a
constant integer-valued function.  The proof then chooses a coefficient above
`natDegree (f * g)`, observes that it is zero, and concludes that the entire
coefficient function is zero.  Thus it proves the result only by incorrectly
forcing `f * g = 0`.

The corrected statement fixes the hypothesis to the intended one:

`∀ n, ∃ a : ℤ, (f * g).coeff n = a`.

With this weaker and correct assumption, we can no longer conclude `f * g = 0`.
Instead, the corrected proof clears denominators to obtain integer polynomials
`F, G` and nonzero integers `bf, bg` with `F = bf • f` and `G = bg • g` after
mapping to `ℚ[X]`.

-/

theorem Dummit_Foote_exercise_9_3_2_corrected {f g : Polynomial ℚ} (i j : ℕ)
    (hfg : ∀ n : ℕ, ∃ a : ℤ, (f * g).coeff n = a) :
    ∃ a : ℤ, f.coeff i * g.coeff j = a := by
  classical
  -- Clear denominators: get integer polynomials F, G and nonzero integers bf, bg
  -- with `F.map (Int.castRingHom ℚ) = bf • f` and similarly for g.
  obtain ⟨bf, hbf⟩ :=
    IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) f
  obtain ⟨bg, hbg⟩ :=
    IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) g
  set F : Polynomial ℤ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) f
  set G : Polynomial ℤ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) g
  have bf_ne : (bf : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero bf
  have bg_ne : (bg : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero bg
  have bfbg_neQ : (((bf : ℤ) * bg : ℤ) : ℚ) ≠ 0 := by
    push_cast
    exact mul_ne_zero (Int.cast_ne_zero.mpr bf_ne) (Int.cast_ne_zero.mpr bg_ne)
  -- Coefficient-wise read-off of `hbf` and `hbg`.
  have hFcoeff : ∀ k, ((F.coeff k : ℤ) : ℚ) = ((bf : ℤ) : ℚ) * f.coeff k := by
    intro k
    have h := Polynomial.ext_iff.mp hbf k
    rw [Polynomial.coeff_map, Polynomial.coeff_smul, zsmul_eq_mul] at h
    convert h using 1
  have hGcoeff : ∀ k, ((G.coeff k : ℤ) : ℚ) = ((bg : ℤ) : ℚ) * g.coeff k := by
    intro k
    have h := Polynomial.ext_iff.mp hbg k
    rw [Polynomial.coeff_map, Polynomial.coeff_smul, zsmul_eq_mul] at h
    convert h using 1
  -- Each coefficient of `F * G` is divisible by `bf * bg` in `ℤ`.
  have hFGdvd : ∀ k, ((bf : ℤ) * bg) ∣ (F * G).coeff k := by
    intro k
    obtain ⟨a, ha⟩ := hfg k
    refine ⟨a, ?_⟩
    have hmul : (F * G).map (algebraMap ℤ ℚ) = ((bf : ℤ) * bg) • (f * g) := by
      rw [Polynomial.map_mul, hbf, hbg, smul_mul_smul_comm]
    have h := Polynomial.ext_iff.mp hmul k
    rw [Polynomial.coeff_map, Polynomial.coeff_smul, zsmul_eq_mul] at h
    rw [ha] at h
    have hQ : (((F * G).coeff k : ℤ) : ℚ) = (((bf : ℤ) * bg * a : ℤ) : ℚ) := by
      have hLHS : ((F * G).coeff k : ℚ) = (algebraMap ℤ ℚ) ((F * G).coeff k) := by simp
      rw [hLHS, h]; push_cast; ring
    exact_mod_cast hQ
  -- Hence `bf * bg | content(F * G) = content(F) * content(G)` (Gauss's lemma).
  have hContent_dvd : ((bf : ℤ) * bg) ∣ (F * G).content := by
    rw [Polynomial.content]
    exact Finset.dvd_gcd (fun k _ => hFGdvd k)
  rw [Polynomial.content_mul] at hContent_dvd
  obtain ⟨γ, hγ⟩ := hContent_dvd
  obtain ⟨α, hα⟩ := Polynomial.content_dvd_coeff (p := F) i
  obtain ⟨β, hβ⟩ := Polynomial.content_dvd_coeff (p := G) j
  refine ⟨γ * α * β, ?_⟩
  -- In `ℚ`: `(bf*bg) * (f.coeff i * g.coeff j) = F.coeff i * G.coeff j`
  --                                            = `(F.content * α) * (G.content * β)`
  --                                            = `(bf * bg * γ) * α * β`.
  have lhs : (((bf : ℤ) * bg : ℤ) : ℚ) * (f.coeff i * g.coeff j)
           = ((F.coeff i : ℤ) : ℚ) * ((G.coeff j : ℤ) : ℚ) := by
    rw [hFcoeff i, hGcoeff j]
    push_cast; ring
  have rhs : ((F.coeff i : ℤ) : ℚ) * ((G.coeff j : ℤ) : ℚ)
           = (((bf : ℤ) * bg : ℤ) : ℚ) * ((γ * α * β : ℤ) : ℚ) := by
    have hαQ : ((F.coeff i : ℤ) : ℚ) = ((F.content : ℤ) : ℚ) * ((α : ℤ) : ℚ) := by
      exact_mod_cast hα
    have hβQ : ((G.coeff j : ℤ) : ℚ) = ((G.content : ℤ) : ℚ) * ((β : ℤ) : ℚ) := by
      exact_mod_cast hβ
    have hγQ : ((F.content * G.content : ℤ) : ℚ)
             = (((bf : ℤ) * bg : ℤ) : ℚ) * ((γ : ℤ) : ℚ) := by
      exact_mod_cast hγ
    rw [hαQ, hβQ]
    have step : ((F.content : ℤ) : ℚ) * α * (((G.content : ℤ) : ℚ) * β)
              = ((F.content * G.content : ℤ) : ℚ) * α * β := by push_cast; ring
    rw [step, hγQ]; push_cast; ring
  exact mul_left_cancel₀ bfbg_neQ (lhs.trans rhs)
