import Mathlib

namespace MathlibPlus.Open.Analysis

/--
The Bessel correction and exact frame weight from admitted Claim 9362,
using the admitted multiplier formula from Claim 9358 and its stated
parameter range from Claim 9363.
-/
def besselCorrectionAndExactFrameWeight : Prop :=
  ∀ (ε : ℝ), 0 ≤ ε → ε < 1 / 2 →
    ∃ (Pε Wε : ℝ → ℝ) (Aε : ℝ → ℂ),
      Pε = (fun t : ℝ => (1 + t ^ 2) ^ (-5 / 8 + ε / 4)) ∧
      Aε =
        (fun t : ℝ =>
          ((-1 / 2 : ℂ) + ε + Complex.I * t) / 2 *
            Complex.Gamma (3 / 4 - ε / 2 - Complex.I * t / 2)) ∧
      Wε =
        (fun t : ℝ =>
          2 * Real.cosh (Real.pi * t / 2) *
            (1 + t ^ 2) ^ (-5 / 4 + ε / 2) *
            Complex.normSq (Aε t))

end MathlibPlus.Open.Analysis
