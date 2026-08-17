import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0128

/-- Claim 18139: the Weyl boundary value of the normalized Poisson field is
`x cot (πx)`, at the square-root parameter `x`. -/
noncomputable def weylFunction_18139 : Prop :=
  ∀ (x : ℝ), Real.sin (Real.pi * x) ≠ 0 →
    deriv (fun r : ℝ => Real.sin (x * r) / Real.sin (Real.pi * x)) Real.pi =
      x * Real.cot (Real.pi * x)

end MathlibPlus.Open.ResearchFormalization.R0128
