import Mathlib

namespace MathlibPlus.Analysis

/-- Admitted claim 4507: the centered dilation acting on a complex-valued
function on the real line. -/
noncomputable def centeredDilation_claim4507 (c : ℝ) (h : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (Real.exp (-c / 2) : ℂ) * h (Real.exp (-c) * x)

end MathlibPlus.Analysis
