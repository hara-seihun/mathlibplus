import Mathlib
import MathlibPlus.LinearAlgebra.CompletedBezout

open scoped BigOperators

namespace MathlibPlus.Open.LinearAlgebra

/-- Exact rank-four determinant identity for the completed Bezout section of the
positive two-atom factorial-moment model. -/
def rankFourDeterminantPolynomial : Prop :=
  ∀ ε : ℝ, 0 < ε →
    let h : ℕ → ℝ := fun j =>
      (1 + ε * ((4 : ℝ)⁻¹) ^ j) / (Nat.factorial (2 * j) : ℝ)
    let C : Matrix (Fin 4) (Fin 4) ℝ :=
      MathlibPlus.LinearAlgebra.CompletedBezout.completedBezoutMatrix h 4
    Matrix.det C =
      (ε + 1) *
        (2097152 * ε ^ 7 +
          55500425216 * ε ^ 6 -
          17984666444304 * ε ^ 5 +
          54202816766341 * ε ^ 4 -
          1270038175574324 * ε ^ 3 +
          1555972249399296 * ε ^ 2 -
          9009293588168704 * ε +
          9007199254740992) /
        903931901687350576475327692800000

end MathlibPlus.Open.LinearAlgebra
