import Mathlib

namespace MathlibPlus.Open.Analysis.SymmetricDivisorFlux15335_15336

noncomputable section

/-- The critical-line quartic from the O-0314 divisor relocation pair. -/
private def lineQuartic15332 (b : ℝ) (z : ℂ) : ℂ :=
  (z ^ 2 + (b : ℂ) ^ 2) ^ 2

/-- The off-axis conjugate-pair quartic from the O-0314 divisor relocation pair. -/
private def offQuartic15332 (a b : ℝ) (z : ℂ) : ℂ :=
  (z ^ 2 - ((a : ℂ) + (b : ℂ) * Complex.I) ^ 2) *
    (z ^ 2 - ((a : ℂ) - (b : ℂ) * Complex.I) ^ 2)

/-- Imaginary-axis positivity and phase equality from admitted claim 15335. -/
def imaginaryAxisPositivityAndPhaseEquality15335 : Prop :=
  ∀ a b t : ℝ, 0 < a → a < 1 / 2 → 0 < b →
    lineQuartic15332 b ((t : ℂ) * Complex.I) =
        (((b ^ 2 - t ^ 2) ^ 2 : ℝ) : ℂ) ∧
      0 ≤ (b ^ 2 - t ^ 2) ^ 2 ∧
      Complex.arg (lineQuartic15332 b ((t : ℂ) * Complex.I)) = 0 ∧
      offQuartic15332 a b ((t : ℂ) * Complex.I) =
        ((((t ^ 2 + a ^ 2 - b ^ 2) ^ 2 + 4 * a ^ 2 * b ^ 2 : ℝ)) : ℂ) ∧
      0 < (t ^ 2 + a ^ 2 - b ^ 2) ^ 2 + 4 * a ^ 2 * b ^ 2 ∧
      Complex.arg (offQuartic15332 a b ((t : ℂ) * Complex.I)) = 0 ∧
      (∀ u : ℝ, 0 < u →
        Complex.arg (lineQuartic15332 b (((b - u : ℝ) : ℂ) * Complex.I)) =
          Complex.arg (lineQuartic15332 b (((b + u : ℝ) : ℂ) * Complex.I)))

/-- Symmetric relocation is invisible to normal logarithmic flux and to the
corresponding tangential argument velocity on the symmetry axis, as in claim
15336. -/
def symmetricRelocationInvisibleFlux15336 : Prop :=
  ∀ a b t : ℝ, 0 < a → a < 1 / 2 → 0 < b →
    (lineQuartic15332 b ((t : ℂ) * Complex.I) ≠ 0 →
      (deriv (lineQuartic15332 b) ((t : ℂ) * Complex.I) /
          lineQuartic15332 b ((t : ℂ) * Complex.I)).re = 0 ∧
        (Complex.I *
            (deriv (lineQuartic15332 b) ((t : ℂ) * Complex.I) /
              lineQuartic15332 b ((t : ℂ) * Complex.I))).im = 0) ∧
    (offQuartic15332 a b ((t : ℂ) * Complex.I) ≠ 0 →
      (deriv (offQuartic15332 a b) ((t : ℂ) * Complex.I) /
          offQuartic15332 a b ((t : ℂ) * Complex.I)).re = 0 ∧
        (Complex.I *
            (deriv (offQuartic15332 a b) ((t : ℂ) * Complex.I) /
              offQuartic15332 a b ((t : ℂ) * Complex.I))).im = 0)

end

end MathlibPlus.Open.Analysis.SymmetricDivisorFlux15335_15336
