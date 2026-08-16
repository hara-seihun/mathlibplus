import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.FormalizationBatch13410

noncomputable section

/-- The all-prime kernel, using the admitted power-series expansion. -/
def allPrimeKernel (x : ℝ) : ℂ :=
  ∑' k : ℕ, ((-(x : ℂ)) ^ k) /
    ((k.factorial : ℂ) * riemannZeta (k + 2))

/-- Claim 13410: the Mellin transform of the all-prime kernel. -/
def allPrimeKernelMellinTransform : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 →
    (MeasureTheory.integral
      (volume.restrict (Set.Ioi (0 : ℝ)))
      (fun x => allPrimeKernel x * Complex.cpow (x : ℂ) (s - 1))) =
      Complex.Gamma s / riemannZeta (2 - s)

/-- The finite Euler product from the admitted cutoff definition. -/
def finiteEulerProduct (y : ℕ) (z : ℂ) : ℂ :=
  Finset.prod ((Finset.range (y + 1)).filter Nat.Prime)
    (fun p => (1 : ℂ) - Complex.cpow (p : ℂ) (-z))

/-- The Mellin-line point `c + it`. -/
def mellinLine (c t : ℝ) : ℂ := (c : ℂ) + (t : ℂ) * Complex.I

/-- The exact finite-kernel spectral weight used in the prime-step correlation. -/
def finiteKernelWeight (y : ℕ) (c t : ℝ) : ℝ :=
  ‖Complex.Gamma (mellinLine c t)‖ ^ 2 *
    ‖finiteEulerProduct y (2 - mellinLine c t)‖ ^ 2

/-- The exact normalized prime-step correlation. -/
def primeStepCorrelation (y p : ℕ) (c : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (∫ t : ℝ,
      finiteKernelWeight y c t * Real.cos (t * Real.log (p : ℝ)))

/-- Claim 13419: the `{2,3,5}` to `7` prime step is negative at `c = 1.35`. -/
def explicitFailedPrimeStepSign : Prop :=
  primeStepCorrelation 5 7 (27 / 20 : ℝ) < 0

end

end MathlibPlus.Open.Analysis.FormalizationBatch13410
