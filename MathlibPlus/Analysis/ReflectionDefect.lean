import Mathlib

namespace MathlibPlus.Analysis

/-- The additive reflection defect is identically zero exactly at the
reflection-fixed parameter `b = 1 / 2`. -/
theorem reflectionDefect_vanishes_iff (b : ℝ) :
    (∀ u : ℝ, (2 * b - 1) * Real.cosh (u / 2) = 0) ↔ b = 1 / 2 := by
  constructor
  · intro h
    have h0 := h 0
    norm_num at h0 ⊢
    linarith
  · intro hb u
    rw [hb]
    norm_num

/-- Claim 4617: a complex-valued function has the xi reflection symmetry. -/
def HasXiReflection (xi : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, xi (1 - z) = xi z

end MathlibPlus.Analysis
