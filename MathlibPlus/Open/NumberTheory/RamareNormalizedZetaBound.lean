import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MathlibPlus.Open.NumberTheory

/-- Ramaré's normalized zeta bound, stated on the real half-line using the
real part of the complex Riemann zeta function. -/
def ramareNormalizedZetaBound : Prop :=
  ∀ s : ℝ, 1 < s →
    (s - 1) * (riemannZeta (s : ℂ)).re ≤
      Real.exp (Real.eulerMascheroniConstant * (s - 1))

end MathlibPlus.Open.NumberTheory
