import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.AnalyticNumberTheory

/-- Claim 1694 (Bastien--Rogalski): for every real `s > 1`, the normalized
zeta value is bounded by the corresponding real power of two.  The real part
makes the convention for Mathlib's complex-valued Riemann zeta explicit. -/
def bastienRogalskiNormalizedZetaBound_claim1694 : Prop :=
  ∀ s : ℝ, 1 < s →
    (s - 1) * (riemannZeta (s : ℂ)).re < Real.rpow 2 (s - 1)

/-- Claim 6827 (Mellin transform of the staircase).  The conventional
fundamental strip `0 < Re(s) < 1` is made explicit, and on positive real `x`
the complex power is written using the principal logarithm branch. -/
def staircaseMellinTransform_claim6827 : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 →
    (∫ x in Set.Ioi (0 : ℝ),
        ((Int.fract x : ℝ) : ℂ) * Complex.exp ((-s - 1) * (Real.log x : ℂ))) =
      -riemannZeta s / s

end MathlibPlus.Open.AnalyticNumberTheory
