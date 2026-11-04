import Mathlib
import Pistis

theorem helper_kernel_support_step1 {I J : Type*} {x : J → ℝ} {y : I → ℝ} {j : J} {s : I}
    (h : x j * y s ≠ 0) : x j * y s ≠ 0 := h
