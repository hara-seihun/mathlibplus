import Mathlib
import MathlibPlus.Open.Research.FormalizationBatchGammaJump

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace MathlibPlus.Open.Research.FormalizationBatch.O0191Parity

noncomputable section

abbrev HLine : Type := MeasureTheory.Lp ℝ 2 (volume : Measure ℝ)

/-- The exact cutoff carrier `H_R = L²((-R,R))`. -/
abbrev H_R (R : ℝ) : Type :=
  MeasureTheory.Lp ℝ 2 (volume.restrict (Ioo (-R) R))

noncomputable def cutoffRestriction (R : ℝ) : HLine →L[ℝ] H_R R :=
  MeasureTheory.LpToLpRestrictCLM ℝ ℝ ℝ (volume : Measure ℝ) 2
    (Ioo (-R) R)

noncomputable def cutoffExtension (R : ℝ) : H_R R →L[ℝ] HLine :=
  (cutoffRestriction R).adjoint

noncomputable def unitaryTranslation (ell : ℝ) : HLine →ₗᵢ[ℝ] HLine :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ (fun x : ℝ => x + ell)
    (MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) ell)

noncomputable def compressedTranslation (R ell : ℝ) : H_R R →L[ℝ] H_R R :=
  (cutoffRestriction R).comp
    ((unitaryTranslation ell).toContinuousLinearMap.comp (cutoffExtension R))

noncomputable def unitaryReflection : HLine →ₗᵢ[ℝ] HLine :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ (fun x : ℝ => -x)
    (MeasureTheory.Measure.measurePreserving_neg (volume : Measure ℝ))

noncomputable def reflection (R : ℝ) : H_R R →L[ℝ] H_R R :=
  (cutoffRestriction R).comp
    (unitaryReflection.toContinuousLinearMap.comp (cutoffExtension R))

def cutoffInner {R : ℝ} (f g : H_R R) : ℝ :=
  inner ℝ f g

noncomputable def jumpOperator (R ell : ℝ) : H_R R →L[ℝ] H_R R :=
  2 • ContinuousLinearMap.id ℝ (H_R R) -
    compressedTranslation R ell - (compressedTranslation R ell).adjoint

def jumpBilinear (R ell : ℝ) (f g : H_R R) : ℝ :=
  2 * cutoffInner f g -
    cutoffInner (compressedTranslation R ell f) g -
      cutoffInner f (compressedTranslation R ell g)

noncomputable def primeCutoff (R : ℝ) : Finset ℕ :=
  (Finset.Icc 2 (Nat.ceil (Real.exp (2 * R)))).filter
    (fun n => (n : ℝ) < Real.exp (2 * R))

noncomputable def completedLForm (R : ℝ) (f g : H_R R) : ℝ :=
  (∫ ell : ℝ in Ioi (0 : ℝ),
      MathlibPlus.Open.Research.FormalizationBatchGammaJump.gammaJumpWeight ell *
        jumpBilinear R ell f g) +
    ∑ n ∈ primeCutoff R,
      MathlibPlus.Open.Research.FormalizationBatchGammaJump.primeJumpCoefficient n *
        jumpBilinear R (Real.log (n : ℝ)) f g

noncomputable def cutoffKappa (R : ℝ) : ℝ :=
  2 * ∑ n ∈ primeCutoff R,
      MathlibPlus.Open.Research.FormalizationBatchGammaJump.primeJumpCoefficient n +
    Real.log Real.pi - (Complex.digamma (1 / 4 : ℂ)).re

noncomputable def pProfile (x : ℝ) : ℝ :=
  (Real.exp (x / 2) + Real.exp (-x / 2)) / Real.sqrt 2

noncomputable def mProfile (x : ℝ) : ℝ :=
  (Real.exp (x / 2) - Real.exp (-x / 2)) / Real.sqrt 2

noncomputable def pCoordinate (R : ℝ) (f : H_R R) : ℝ :=
  ∫ x : ℝ in Ioo (-R) R, (f : ℝ → ℝ) x * pProfile x

noncomputable def mCoordinate (R : ℝ) (f : H_R R) : ℝ :=
  ∫ x : ℝ in Ioo (-R) R, (f : ℝ → ℝ) x * mProfile x

noncomputable def completedKForm (R : ℝ) (f g : H_R R) : ℝ :=
  completedLForm R f g - cutoffKappa R * cutoffInner f g

noncomputable def completedQForm (R : ℝ) (f g : H_R R) : ℝ :=
  (completedLForm R f g + pCoordinate R f * pCoordinate R g) -
    (cutoffKappa R * cutoffInner f g + mCoordinate R f * mCoordinate R g)

def evenSector (R : ℝ) (f : H_R R) : Prop := reflection R f = f

def oddSector (R : ℝ) (f : H_R R) : Prop := reflection R f = -f

/-- Claim 14944: reflection preserves the completed cutoff channels, the
boundary profiles have the stated parity, and the two parity restrictions of
`Q_R` are the displayed `K_R` plus/minus rank-one forms. -/
def claim_14944 : Prop :=
  ∀ R : ℝ, 0 < R →
    (∀ ell : ℝ,
      (reflection R).comp (jumpOperator R ell) =
        (jumpOperator R ell).comp (reflection R)) ∧
    (∀ f g : H_R R,
      cutoffInner (reflection R f) g = cutoffInner f (reflection R g)) ∧
    (∀ f g : H_R R,
      completedKForm R (reflection R f) g =
        completedKForm R f (reflection R g)) ∧
    (∀ x : ℝ,
      pProfile (-x) = pProfile x ∧ mProfile (-x) = -mProfile x) ∧
    (∀ f : H_R R,
      pCoordinate R (reflection R f) = pCoordinate R f ∧
        mCoordinate R (reflection R f) = -mCoordinate R f) ∧
    (∀ f : H_R R, evenSector R f →
      completedQForm R f f = completedKForm R f f + pCoordinate R f ^ 2) ∧
    (∀ f : H_R R, oddSector R f →
      completedQForm R f f = completedKForm R f f - mCoordinate R f ^ 2) ∧
    (∀ f g : H_R R, evenSector R f → oddSector R g →
      cutoffInner f g = 0 ∧
        completedQForm R (f + g) (f + g) =
          completedQForm R f f + completedQForm R g g)

end

end MathlibPlus.Open.Research.FormalizationBatch.O0191Parity
