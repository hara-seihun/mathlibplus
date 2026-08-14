import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The Fourier-normalized order-zero Hermite function used by Claim 2392. -/
def fourierNormalizedHermiteZero (x : ℝ) : ℝ :=
  Real.rpow (2 * Real.pi) (1 / 4 : ℝ) * Real.exp (-Real.pi * x ^ 2)

/-- The physicists' fourth Hermite polynomial. -/
def hermiteFourPolynomial (x : ℝ) : ℝ :=
  16 * x ^ 4 - 48 * x ^ 2 + 12

/-- The Fourier-normalized order-four Hermite function used by Claim 2392. -/
def fourierNormalizedHermiteFour (x : ℝ) : ℝ :=
  Real.rpow (2 * Real.pi) (1 / 4 : ℝ) /
      Real.sqrt ((2 : ℝ) ^ 4 * (Nat.factorial 4 : ℝ)) *
    hermiteFourPolynomial (Real.sqrt (2 * Real.pi) * x) *
      Real.exp (-Real.pi * x ^ 2)

def hermiteIntegral (f : ℝ → ℝ) : ℝ := ∫ x : ℝ, f x

def hermiteSecondMoment (f : ℝ → ℝ) : ℝ := ∫ x : ℝ, x ^ 2 * f x

/--
Claim 2392: the exact integrals and second moments of the order-zero and
order-four Fourier-normalized Hermite functions, including the positive
center constant.
-/
def exactHermiteIntegrals2392 : Prop :=
  let i₀ := hermiteIntegral fourierNormalizedHermiteZero
  let i₄ := hermiteIntegral fourierNormalizedHermiteFour
  let m₀ := hermiteSecondMoment fourierNormalizedHermiteZero
  let m₄ := hermiteSecondMoment fourierNormalizedHermiteFour
  i₀ = Real.rpow (2 * Real.pi) (1 / 4 : ℝ) ∧
    i₄ / i₀ = Real.sqrt 6 / 4 ∧
    m₀ = i₀ / (2 * Real.pi) ∧
    m₄ = 9 * i₄ / (2 * Real.pi) ∧
    m₄ - (i₄ / i₀) * m₀ =
      Real.rpow 2 (3 / 4 : ℝ) * Real.sqrt 3 /
        Real.rpow Real.pi (3 / 4 : ℝ) ∧
    0 < Real.rpow 2 (3 / 4 : ℝ) * Real.sqrt 3 /
      Real.rpow Real.pi (3 / 4 : ℝ)

end

end MathlibPlus.Open.Analysis
