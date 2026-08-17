import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0227Smoothing

noncomputable section

/-- The family appearing in the smoothed transform of Claim 19014. -/
noncomputable def adversarialFamily (a c : ℝ) (z : ℂ) : ℂ :=
  (c : ℂ) + Complex.cosh ((a : ℂ) * z)

/-- The removable extension of `sinh (R z) / (R z)`. -/
noncomputable def smoothingKernel (R : ℝ) (z : ℂ) : ℂ :=
  if z = 0 then 1 else
    Complex.sinh ((R : ℂ) * z) / ((R : ℂ) * z)

/-- The complete smoothed transform named in Claim 19014. -/
noncomputable def smoothedTransform (a c R : ℝ) (z : ℂ) : ℂ :=
  adversarialFamily a c z * smoothingKernel R z ^ 4

/-- Claim 19014: for every positive smoothing scale, the removable entire
kernel has the prescribed value and quotient away from zero, and the named
smoothed transform is `A_{a,c}(z) U_R(z)^4` without adding restrictions on
`a` or `c`. -/
def smoothingKernel_claim19014 : Prop :=
  ∀ R : ℝ, 0 < R →
    smoothingKernel R 0 = 1 ∧
      (∀ z : ℂ, z ≠ 0 →
        smoothingKernel R z =
          Complex.sinh ((R : ℂ) * z) / ((R : ℂ) * z)) ∧
      Differentiable ℂ (smoothingKernel R) ∧
        ∀ (a c : ℝ) (z : ℂ),
          smoothedTransform a c R z =
            adversarialFamily a c z * smoothingKernel R z ^ 4

end

end MathlibPlus.Open.ResearchFormalization.R0227Smoothing
