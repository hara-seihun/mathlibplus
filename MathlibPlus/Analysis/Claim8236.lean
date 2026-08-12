import Mathlib

namespace MathlibPlus.Analysis.Claim8236

/-- The radial tangent defect, with the source's first and second derivatives
represented by `deriv` and `deriv (deriv ·)`. -/
noncomputable def radialTangentDefect (G : ℝ → ℝ) (a : ℝ) : ℝ :=
  a ^ 2 * (deriv G a) ^ 2 -
    a * (G a) * deriv G a -
    a ^ 2 * deriv (deriv G) a

end MathlibPlus.Analysis.Claim8236
