import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.R0101

/-- Claim 17943: the divisor-fiber coordinate is one half of the displayed logarithm. -/
def divisor_fiber_coordinate (k m : ℕ) (ell : ℝ) : Prop :=
  m ∣ k → ell = (1 / 2 : ℝ) * Real.log ((k : ℝ) / (m : ℝ) ^ 2)

end MathlibPlus.Open.FormalizationBatch.R0101
