import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.Analysis

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
open MeasureTheory

/-- The Fourier source in Claim 46345. -/
def sourceFourier (w : SchwartzMap ℝ ℝ) (x : ℝ) : ℂ :=
  ∫ u : ℝ,
    Complex.ofReal (w u) *
      Complex.exp (Complex.I * Complex.ofReal (x * u))

/-- Claim 46345. -/
def claim46345 : Prop :=
  ∀ (w : SchwartzMap ℝ ℝ) (x : ℝ),
    (deriv (sourceFourier w) x) ^ 2 -
        sourceFourier w x * deriv (fun y => deriv (sourceFourier w) y) x =
      (1 / 2 : ℂ) *
        ∫ u : ℝ, ∫ v : ℝ,
          Complex.ofReal ((u - v) ^ 2) * Complex.ofReal (w u) *
            Complex.ofReal (w v) *
            Complex.exp (Complex.I * Complex.ofReal (x * (u + v)))

end
end MathlibPlus.Open.FormalizationBatch.Analysis
