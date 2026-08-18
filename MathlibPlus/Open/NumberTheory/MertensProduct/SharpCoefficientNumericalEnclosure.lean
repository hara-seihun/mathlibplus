import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.PrimeCounting

namespace MathlibPlus.Open.NumberTheory.MertensProduct

/-- The numerical enclosure and 36-place decimal-prefix interval for the
sharp Mertens-prime-product coefficient. -/
def sharpCoefficientNumericalEnclosure : Prop :=
  let primeProduct283 : ℝ :=
    ∏ p ∈ Nat.primesLE 283, (p : ℝ) / ((p : ℝ) - 1)
  let coefficient : ℝ :=
    Real.log 286 *
      (Real.exp (-Real.eulerMascheroniConstant) * primeProduct283 - Real.log 286)
  let decimalPrefix : ℝ := 0.482761856265219690669858626593363196
  0.4827618562651 < coefficient ∧
    coefficient < 0.4827618562654 ∧
    decimalPrefix ≤ coefficient ∧
    coefficient < decimalPrefix + 1 / (10 : ℝ) ^ 36

end MathlibPlus.Open.NumberTheory.MertensProduct
