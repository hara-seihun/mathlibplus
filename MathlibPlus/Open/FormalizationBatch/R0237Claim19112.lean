import Mathlib

open Polynomial

namespace MathlibPlus.Open.FormalizationBatch.R0237Claim19112

private noncomputable def denominator : Polynomial ℝ :=
  1 - X

/-- The numerator-free Euler factor as an element of the polynomial fraction
field, retaining the denominator rather than replacing the factor by a free
real-valued callback. -/
private noncomputable def genuineEulerFactor :
    FractionRing (Polynomial ℝ) :=
  algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)) 1 /
    algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)) denominator

private noncomputable def counterfeitEulerFactor
    (p : ℕ) (b : ℝ) : FractionRing (Polynomial ℝ) :=
  algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ))
      (1 + C b * X + C (p : ℝ) * X ^ 2) /
    algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)) denominator

private noncomputable def residual
    (A : FractionRing (Polynomial ℝ)) : FractionRing (Polynomial ℝ) :=
  algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)) denominator * A -
    algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)) 1

/-- Claim 19112: simultaneous residual vanishing at every prime is the
numerator-free condition, while the positive counterfeit numerator leaves the
explicit nonzero polynomial value at every nonzero test point. -/
def claim19112_residualPolynomialDetection : Prop :=
  (∀ (p : ℕ), p.Prime →
    residual genuineEulerFactor = 0) ∧
  (∀ (p : ℕ), p.Prime → ∀ (b t : ℝ), 0 < b → t ≠ 0 →
    residual (counterfeitEulerFactor p b) =
      algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ))
        (C b * X + C (p : ℝ) * X ^ 2) ∧
      Polynomial.eval t (C b * X + C (p : ℝ) * X ^ 2) ≠ 0)

end MathlibPlus.Open.FormalizationBatch.R0237Claim19112
