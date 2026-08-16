import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-! Claim 11380: the explicit zero family and curvature endpoint. -/

def record14Carrier (z : ℂ) : ℂ :=
  2 * Complex.cosh z + Complex.cosh (2 * z)

def record14Endpoint : ℝ :=
  Real.arcosh ((1 + Real.sqrt 3) / 2)

def record14OddImaginaryShift (k : ℤ) : ℂ :=
  (2 * (k : ℂ) + 1) * (Real.pi : ℂ) * Complex.I

def record14PositiveZero (k : ℤ) : ℂ :=
  (record14Endpoint : ℂ) + record14OddImaginaryShift k

def record14NegativeZero (k : ℤ) : ℂ :=
  -(record14Endpoint : ℂ) + record14OddImaginaryShift k

def record14AmplitudeCurvature (x : ℝ) : ℝ :=
  (iteratedDeriv 2 record14Carrier
          ((x : ℂ) + (Real.pi : ℂ) * Complex.I) /
        record14Carrier ((x : ℂ) + (Real.pi : ℂ) * Complex.I) -
      (deriv record14Carrier ((x : ℂ) + (Real.pi : ℂ) * Complex.I) /
          record14Carrier ((x : ℂ) + (Real.pi : ℂ) * Complex.I)) ^ 2).re

def explicitRecord14OffAxisZeros : Prop :=
  (∀ k : ℤ, record14Carrier (record14PositiveZero k) = 0) ∧
    (∀ k : ℤ, record14Carrier (record14NegativeZero k) = 0) ∧
    (∀ k : ℤ, (record14PositiveZero k).re = record14Endpoint) ∧
    (∀ k : ℤ, (record14NegativeZero k).re = -record14Endpoint) ∧
    (∀ x : ℝ, |x| < record14Endpoint →
      record14Carrier ((x : ℂ) + (Real.pi : ℂ) * Complex.I) ≠ 0 ∧
        record14AmplitudeCurvature x < 0)

end MathlibPlus.Open.ResearchFormalizationBatch
