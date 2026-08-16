import Mathlib

open scoped BigOperators
open MeasureTheory Set

namespace MathlibPlus.Open.ResearchFormalization.O0319Claim14175

noncomputable section

/-- The scalar Laplace transform on the nonnegative real half-line. -/
noncomputable def scalarLaplaceTransform (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ,
    (f u : ℂ) * Complex.exp (-z * (u : ℂ)) ∂
      (Measure.restrict volume (Set.Ici (0 : ℝ)))

/-- The coefficient of the scalar prime-side logarithmic derivative field. -/
def scalarPrimeCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then
    (ArithmeticFunction.vonMangoldt n : ℝ) * f (Real.log (n : ℝ))
  else 0

/-- Nonnegative prime coefficients for the scalar architecture. -/
def primeCoefficientsNonnegative (f : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, 0 ≤ scalarPrimeCoefficient f n

/-- Existence of the displayed Laplace integral throughout the right half-plane. -/
def scalarLaplaceIntegrable (f : ℝ → ℝ) : Prop :=
  ∀ z : ℂ, 0 < z.re →
    Integrable (fun u : ℝ =>
      (f u : ℂ) * Complex.exp (-z * (u : ℂ)))
      (Measure.restrict volume (Set.Ici (0 : ℝ)))

/-- The continuous nonnegative scalar weight on `[0,∞)`, with its exact
right-half-plane Laplace carrier. -/
def continuousNonnegativeScalarWeight (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici (0 : ℝ)) ∧
    (∀ u : ℝ, u ∈ Set.Ici (0 : ℝ) → 0 ≤ f u) ∧
    primeCoefficientsNonnegative f ∧
    scalarLaplaceIntegrable f

/-- One-signed deletability of every zero through the scalar Laplace kernel. -/
def oneSignedZeroKernel (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 < x →
    0 ≤ (scalarLaplaceTransform f
      ((x : ℂ) + (y : ℂ) * Complex.I)).re

/-- Cancellation of the archimedean endpoint mass. -/
def endpointMassCancellation (f : ℝ → ℝ) : Prop :=
  f 0 = 0

/-- Nontriviality of a scalar weight on the nonnegative half-line. -/
def nontrivialScalarWeight (f : ℝ → ℝ) : Prop :=
  ∃ u : ℝ, u ∈ Set.Ici (0 : ℝ) ∧ f u ≠ 0

/-- The three scalar goals cannot hold for a nontrivial weight at once. -/
def scalarPrimeGammaZeroTrilemma : Prop :=
  ¬ ∃ f : ℝ → ℝ,
    continuousNonnegativeScalarWeight f ∧
      oneSignedZeroKernel f ∧
      endpointMassCancellation f ∧
      nontrivialScalarWeight f

/-- The gamma-canceling finite-difference weight. -/
def finiteDifferenceWeight (h u : ℝ) : ℝ :=
  1 - Real.exp (-h * u)

/-- The explicit finite-difference Laplace kernel. -/
def finiteDifferenceLaplaceKernel (h : ℝ) (z : ℂ) : ℂ :=
  1 / z - 1 / (z + (h : ℂ))

/-- Finite differences cancel the endpoint while losing the zero-kernel sign. -/
def finiteDifferenceEndpointAndSignLoss : Prop :=
  ∀ h : ℝ, 0 < h →
    finiteDifferenceWeight h 0 = 0 ∧
      (∀ u : ℝ, 0 ≤ u → 0 ≤ finiteDifferenceWeight h u) ∧
      primeCoefficientsNonnegative (finiteDifferenceWeight h) ∧
      scalarLaplaceIntegrable (finiteDifferenceWeight h) ∧
      (∀ x y : ℝ, 0 < x →
        (scalarLaplaceTransform (finiteDifferenceWeight h)
            ((x : ℂ) + (y : ℂ) * Complex.I) =
          finiteDifferenceLaplaceKernel h
            ((x : ℂ) + (y : ℂ) * Complex.I) ∧
        (finiteDifferenceLaplaceKernel h
            ((x : ℂ) + (y : ℂ) * Complex.I)).re =
          h * (x * (x + h) - y ^ 2) /
            ((x ^ 2 + y ^ 2) * ((x + h) ^ 2 + y ^ 2)))) ∧
      (∀ x y : ℝ, 0 < x → y ^ 2 > x * (x + h) →
        (finiteDifferenceLaplaceKernel h
          ((x : ℂ) + (y : ℂ) * Complex.I)).re < 0) ∧
      ¬ oneSignedZeroKernel (finiteDifferenceWeight h)

/-- Scalar prime/gamma/zero-sign trilemma, with the finite-difference witness. -/
def claim14175 : Prop :=
  scalarPrimeGammaZeroTrilemma ∧
    finiteDifferenceEndpointAndSignLoss

end
end MathlibPlus.Open.ResearchFormalization.O0319Claim14175
