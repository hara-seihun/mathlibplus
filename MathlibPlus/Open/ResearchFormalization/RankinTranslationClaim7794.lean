import MathlibPlus.Open.Analysis.ClosedPhasePairedTranslationKernel
import MathlibPlus.Open.Analysis.AllOrderCheckerboardWickRotation

namespace MathlibPlus.Open.ResearchFormalization.RankinTranslationClaim7794

open MathlibPlus.Open.Analysis
open MeasureTheory

noncomputable section

/-- The zero-phase translation overlap in the closed Gamma radial carrier. -/
def rankinOverlap7794 (α z : ℝ) : ℂ :=
  gammaInner α (fun _ : ℝ => (1 : ℂ))
    (rankinExponential α z (fun _ : ℝ => (1 : ℂ)))

/-- The characteristic function of the reviewed Meixner--Pollaczek measure. -/
def rankinCharacteristic7794 (α x : ℝ) : ℂ :=
  ∫ t : ℝ,
    Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))
      ∂(meixnerPollaczekMeasure α)

/-- The spectral moments corresponding to the skew generator `A = -i T`. -/
def rankinAGeneralizedMoment7794 (α : ℝ) (k : ℕ) : ℂ :=
  ∫ t : ℝ, ((-Complex.I) * (t : ℂ)) ^ k ∂(meixnerPollaczekMeasure α)

/-- The centered moments of the self-adjoint generator `T`. -/
def rankinTMoment7794 (α : ℝ) (k : ℕ) : ℂ :=
  ∫ t : ℝ, (t : ℂ) ^ k ∂(meixnerPollaczekMeasure α)

/--
Claim 7794: the closed translation overlap and the equivalent characteristic
function are the centered sech power, with all derivative and moment
normalizations retained.
-/
def claim7794_translationOverlapAndCenteredMoments : Prop :=
  ∀ α : ℝ, 0 < α →
    (∀ z : ℝ,
      rankinOverlap7794 α z =
        Complex.cpow (sech z : ℂ) (α : ℂ)) ∧
    (∀ x : ℝ,
      rankinCharacteristic7794 α x =
        Complex.cpow (sech x : ℂ) (α : ℂ)) ∧
    (∀ k : ℕ,
      iteratedDeriv k (rankinOverlap7794 α) 0 =
        rankinAGeneralizedMoment7794 α k) ∧
    (∀ k : ℕ,
      iteratedDeriv k (rankinCharacteristic7794 α) 0 =
        ∫ t : ℝ, (Complex.I * (t : ℂ)) ^ k
          ∂(meixnerPollaczekMeasure α)) ∧
    (∀ k : ℕ, rankinTMoment7794 α (2 * k + 1) = 0) ∧
    rankinAGeneralizedMoment7794 α 2 = (-α / 4 : ℂ) ∧
    rankinTMoment7794 α 2 = (α / 4 : ℂ)

end

end MathlibPlus.Open.ResearchFormalization.RankinTranslationClaim7794
