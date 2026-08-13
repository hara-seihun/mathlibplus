import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 17357: the Jacobi theta transformation on the positive real axis.
Here `Θ(y)` is made explicit as the bilateral Gaussian theta series. -/
def jacobiThetaModularity : Prop :=
  ∀ y : ℝ, 0 < y →
    (∑' n : ℤ, Real.exp (-Real.pi * (1 / y) * (n : ℝ) ^ 2)) =
      Real.sqrt y * (∑' n : ℤ, Real.exp (-Real.pi * y * (n : ℝ) ^ 2))

end MathlibPlus.Open.Analysis
