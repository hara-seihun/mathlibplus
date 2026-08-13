import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeSums

/--
Claim 15275: the exact Cauchy-kernel Fourier integral for positive integers.
The oscillatory factor is written in `ℂ`, while the displayed real power and
logarithm are made explicit.  The source does not specify a formal integral
codomain; its exponential factor forces the complex-valued interpretation.
-/
def exactCauchyKernelIntegral : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    let mn : ℝ := (m * n : ℕ)
    let ratio : ℝ := (m : ℝ) / n
    let scale : ℝ := Real.rpow mn (-1 / 2 : ℝ)
    (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ,
          (scale : ℂ) *
              Complex.exp
                (-Complex.I * (t : ℂ) * (Real.log ratio : ℂ)) /
            ((1 / 4 : ℂ) + (t : ℂ) ^ 2) =
      (1 / (max m n : ℝ) : ℂ)

end MathlibPlus.Open.AnalyticNumberTheory.PrimeSums
