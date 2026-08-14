import Mathlib

open Set
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.Research.K0122

/-- The one-sided kernel appearing in the logarithmic phase convolution. -/
def phaseKernel (v : ℝ) : ℝ :=
  Real.exp (-2 * v) / (Real.pi * Real.sqrt (1 - Real.exp (-2 * v)))

/-- Its real Fourier/Mellin symbol, with the one-sided measure made explicit. -/
def phaseKernelSymbol (ξ : ℝ) : ℂ :=
  MeasureTheory.integral (Measure.restrict volume (Set.Ioi (0 : ℝ)))
    (fun v =>
      Complex.exp (-Complex.I * (ξ : ℂ) * (v : ℂ)) * (phaseKernel v : ℂ))

/-- The affine model in the exact convolution formula. -/
def affinePhaseModel (x : ℝ) : ℝ :=
  x / 2 - (1 / 2) * Real.log (4 * Real.pi)

/-- Claim 8849: the two exact moments of the one-sided kernel. -/
def exactKernelMoments : Prop :=
  (MeasureTheory.integral (Measure.restrict volume (Set.Ioi (0 : ℝ))) phaseKernel =
      1 / Real.pi) ∧
    (MeasureTheory.integral (Measure.restrict volume (Set.Ioi (0 : ℝ)))
        (fun v => v * phaseKernel v) = (1 - Real.log 2) / Real.pi)

/-- Claim 8850: the Fourier/Mellin symbol has the stated gamma quotient. -/
def fourierMellinSymbolFormula : Prop :=
  ∀ ξ : ℝ,
    phaseKernelSymbol ξ =
      Complex.Gamma (1 + Complex.I * (ξ : ℂ) / 2) /
        ((2 : ℂ) * (Real.sqrt Real.pi : ℂ) *
          Complex.Gamma (3 / 2 + Complex.I * (ξ : ℂ) / 2))

/-- Claim 8851: the real symbol is zero-free. -/
def zeroFreeRealKernelSymbol : Prop :=
  ∀ ξ : ℝ, phaseKernelSymbol ξ ≠ 0

/-- Claim 8854: convolution of the kernel with the affine model. -/
def exactAffineModelConvolution : Prop :=
  ∀ x : ℝ,
    MeasureTheory.integral (Measure.restrict volume (Set.Ioi (0 : ℝ)))
        (fun v => phaseKernel v * affinePhaseModel (x - v)) =
      (1 / (2 * Real.pi)) * (x - Real.log (2 * Real.pi) - 1)

end MathlibPlus.Open.Research.K0122
