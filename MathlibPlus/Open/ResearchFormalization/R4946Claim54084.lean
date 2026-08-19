import Mathlib
import MathlibPlus.Open.Analysis.FiniteTraceIndistinguishability54091

open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R4946

open MathlibPlus.Open.Analysis.FiniteTraceIndistinguishability54091

private noncomputable def originTimeJet
    (μ : Measure ℝ) (τ : ℝ) (k : ℕ) : ℂ :=
  iteratedDeriv k (fun s : ℝ => heatTransform μ s 0) τ

private noncomputable def originTimeMoment
    (μ : Measure ℝ) (τ : ℝ) (k : ℕ) : ℂ :=
  ∫ u : ℝ,
    (((u ^ (2 * k) * Real.exp (τ * u ^ 2) : ℝ) : ℂ)) ∂μ

private noncomputable def atomMeasure (weight location : ℝ) : Measure ℝ :=
  ENNReal.ofReal weight • Measure.dirac location

private noncomputable def evenAtomPerturbation (n : ℤ) : Measure ℝ :=
  atomMeasure 1 (n : ℝ) + atomMeasure 1 (-(n : ℝ))

private noncomputable def originRow
    (τ : ℝ) (k : ℕ) (n : ℤ) : ℝ :=
  2 * (n : ℝ) ^ (2 * k) * Real.exp (τ * (n : ℝ) ^ 2)

private noncomputable def targetRow (n : ℤ) : ℝ :=
  -2 * Real.exp (targetTime * (n : ℝ) ^ 2) *
    Real.cosh ((n : ℝ) * targetHeight)

/-- R-4946 claim 54084: the origin-time jet is the stated weighted moment
for every positive even discrete super-exponential source, and an even pair
at every odd integer supplies the stated origin and target rows. -/
def claim54084_originTimeJetRows : Prop :=
  (∀ (μ : Measure ℝ), PositiveEvenDiscreteSuperexponential μ →
    ∀ (τ : ℝ) (k : ℕ),
      originTimeJet μ τ k = originTimeMoment μ τ k) ∧
  (∀ (τ : ℝ) (k : ℕ) (n : ℤ), Odd n →
    originTimeMoment (evenAtomPerturbation n) τ k =
        ((originRow τ k n : ℝ) : ℂ) ∧
      heatTransform (evenAtomPerturbation n) targetTime targetPoint =
        ((targetRow n : ℝ) : ℂ))

end MathlibPlus.Open.ResearchFormalization.R4946
