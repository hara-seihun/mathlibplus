import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.NR2FormalizationC0153

noncomputable section

/-- The Gaussian--Hermite source in the logarithmic endpoint-flat family. -/
def logarithmicGaussianHermiteSource (x : ℝ) : ℝ :=
  x ^ 2 * (2 * Real.pi * x ^ 2 - 3) * Real.exp (-Real.pi * x ^ 2)

/-- The Gaussian used to clear the zeroth moment. -/
def logarithmicGaussian (x : ℝ) : ℝ :=
  Real.exp (-Real.pi * x ^ 2)

/-- The logarithmic endpoint-flat order. -/
def logarithmicEndpointOrder (lam : ℝ) : ℕ :=
  2 * ⌊Real.log lam⌋₊ + 2

/-- The endpoint-flat polynomial weight. -/
def logarithmicEndpointWeight (lam x : ℝ) : ℝ :=
  if |x| ≤ lam then
    (1 - x ^ 2 / lam ^ 2) ^ logarithmicEndpointOrder lam
  else 0

/-- The exact Gaussian correction coefficient. -/
def logarithmicCorrectionCoefficient (lam : ℝ) : ℝ :=
  (∫ x in (-lam : ℝ)..lam,
      logarithmicEndpointWeight lam x * logarithmicGaussianHermiteSource x) /
    (∫ x in (-lam : ℝ)..lam,
      logarithmicEndpointWeight lam x * logarithmicGaussian x)

/-- The exact corrected compact source. -/
def logarithmicCorrectedSource (lam x : ℝ) : ℝ :=
  if |x| ≤ lam then
    logarithmicEndpointWeight lam x *
      (logarithmicGaussianHermiteSource x -
        logarithmicCorrectionCoefficient lam * logarithmicGaussian x)
  else 0

/-- The finite arithmetic kernel on the logarithmic coordinate. -/
def logarithmicArithmeticKernel (lam y : ℝ) : ℝ :=
  Real.exp (y / 2) *
    ∑' n : ℕ,
      if 1 ≤ n then
        logarithmicCorrectedSource lam ((n : ℝ) * Real.exp y)
      else 0

/-- The exact finite arithmetic cosine transform `F_λ`. -/
def logarithmicArithmeticTransform (lam : ℝ) (z : ℂ) : ℂ :=
  ∫ y in (-Real.log lam : ℝ)..Real.log lam,
    (logarithmicArithmeticKernel lam y : ℂ) *
      Complex.cos (z * (y : ℂ))

/-- The centered Xi normalization accompanying this transform. -/
def centeredXi (z : ℂ) : ℂ :=
  ((1 / 2 : ℂ) + Complex.I * z) *
      (((1 / 2 : ℂ) + Complex.I * z) - 1) / 2 *
    completedRiemannZeta ((1 / 2 : ℂ) + Complex.I * z)

/-- Claim 2423: the logarithmic strip zero core, together with its explicit
`c = λ²` arithmetic-cutoff consequence. -/
def logarithmicNonrealZeroCore_claim2423 : Prop :=
  ∀ (Y : ℝ),
    0 < Y → Y < 1 / 2 →
    ∃ (K_Y lambdaZero : ℝ),
      0 < K_Y ∧ 1 < lambdaZero ∧
      (∀ (lam : ℝ), lambdaZero ≤ lam →
        ∀ z : ℂ,
          logarithmicArithmeticTransform lam z = 0 →
          |z.im| ≤ Y →
          |z.re| ≥ K_Y * Real.log lam →
            z.im = 0 ∧
              deriv (logarithmicArithmeticTransform lam) z ≠ 0) ∧
      (∀ (lam : ℝ), lambdaZero ≤ lam →
        let c : ℝ := lam ^ 2
        ∀ z : ℂ,
          logarithmicArithmeticTransform lam z = 0 →
          |z.im| ≤ Y → z.im ≠ 0 →
            |z.re| ≤ K_Y * Real.log c)

end

end MathlibPlus.Open.Analysis.NR2FormalizationC0153
