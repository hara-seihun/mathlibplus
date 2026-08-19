import Mathlib

namespace MathlibPlus.Algebra.PolynomialScatteringCounterexample

open Polynomial

/-- The explicit quartic scattering witness from packet R-0226. -/
def polynomialScatteringCounterexample : Prop :=
  let E : Polynomial ℂ := X ^ 2 + 2 * X + 5
  let Eneg : Polynomial ℂ := X ^ 2 - 2 * X + 5
  let Y : Polynomial ℂ := E * Eneg
  Y = X ^ 4 + 6 * X ^ 2 + 25 ∧
    (∀ z : ℂ, Eneg.eval z = E.eval (-z)) ∧
    (∀ z : ℂ,
      Y.eval z = 0 ↔
        z = -1 + 2 * Complex.I ∨
          z = -1 - 2 * Complex.I ∨
          z = 1 + 2 * Complex.I ∨
          z = 1 - 2 * Complex.I) ∧
    (∀ z : ℂ, Y.eval z = 0 → z.re ≠ 0)

end MathlibPlus.Algebra.PolynomialScatteringCounterexample
