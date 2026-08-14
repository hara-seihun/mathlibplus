import Mathlib

namespace MathlibPlus.Open

/-- If two real polynomials have equal derivatives at infinitely many real points
    and agree at one real point, then they are equal. -/
def polynomial_eq_of_derivative_eq_on_infinite_set_and_eval_eq : Prop :=
  ∀ (p q : Polynomial ℝ) (a : ℝ),
    Set.Infinite {x : ℝ |
      Polynomial.eval x (Polynomial.derivative p) =
        Polynomial.eval x (Polynomial.derivative q)} →
    Polynomial.eval a p = Polynomial.eval a q →
    p = q

end MathlibPlus.Open
