import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The Cauchy-kernel Fourier identity, with the positive integer parameters
embedded into the real and complex fields. -/
def cauchyFourierMaxIdentity : Prop :=
  ∀ (m n : ℕ), 0 < m → 0 < n →
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ,
        (((Real.rpow ((m * n : ℕ) : ℝ) (-1 / 2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp
            (-((t : ℂ) * Complex.I *
              ((Real.log ((m : ℝ) / (n : ℝ))) : ℂ))) /
          (((1 / 4 + t ^ 2 : ℝ) : ℂ))) =
      (((1 / (max m n : ℝ) : ℝ) : ℂ))

end
end MathlibPlus.Open.Analysis
