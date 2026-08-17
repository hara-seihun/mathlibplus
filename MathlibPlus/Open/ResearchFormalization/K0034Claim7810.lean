import Mathlib
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Prod
import MathlibPlus.Open.Analysis.ClosedPhasePairedTranslationKernel
import MathlibPlus.Open.ResearchFormalization.SpectralDyadic

open scoped BigOperators MeasureTheory
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.K0034Claim7810

noncomputable section

abbrev C2 := MathlibPlus.Open.ResearchFormalization.SpectralDyadic.C2
abbrev ComplexMeasure := MeasureTheory.ComplexMeasure ℝ

/-- The positive-sign Fourier transform convention used for the translation
kernel. -/
noncomputable def spectralFourierEntry
    (μ : ComplexMeasure) (z : ℝ) : ℂ :=
  MeasureTheory.VectorMeasure.integral μ
    (fun r : ℝ => Complex.exp (Complex.I * (z : ℂ) * (r : ℂ)))
    (ContinuousLinearMap.lsmul ℝ ℂ)

/-- A matrix-valued complex measure whose entries have the displayed density. -/
def spectralMeasureDensity
    (a τ : ℝ) (spectralMeasure : Matrix C2 C2 ComplexMeasure) : Prop :=
  ∀ i j : C2, ∀ E : Set ℝ, MeasurableSet E →
    spectralMeasure i j E =
      ∫ r in E,
        MathlibPlus.Open.ResearchFormalization.SpectralDyadic.spectralDensity
          a τ r i j ∂(MeasureTheory.volume : Measure ℝ)

/-- Claim 7810: the shifted Meixner--Pollaczek outer-product density is a
pointwise rank-one PSD spectral measure and its Fourier transform is the exact
closed phase-paired kernel. -/
def claim7810 : Prop :=
  ∀ (a τ : ℝ), 0 < a →
    ∃ spectralMeasure : Matrix C2 C2 ComplexMeasure,
      (∀ r : ℝ,
        MathlibPlus.Open.Analysis.complexMatrixPosSemidef
          (MathlibPlus.Open.ResearchFormalization.SpectralDyadic.spectralDensity
            a τ r) ∧
        MathlibPlus.Open.ResearchFormalization.SpectralDyadic.rankOneTwo
          (MathlibPlus.Open.ResearchFormalization.SpectralDyadic.spectralDensity
            a τ r)) ∧
      spectralMeasureDensity a τ spectralMeasure ∧
      (∀ z : ℝ, ∀ i j : C2,
        spectralFourierEntry (spectralMeasure i j) z =
          MathlibPlus.Open.Analysis.phaseCoefficientKernel a τ z i j)

end

end MathlibPlus.Open.ResearchFormalization.K0034Claim7810
