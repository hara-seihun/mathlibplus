import Mathlib
import MathlibPlus.Combinatorics.Claim24846

namespace MathlibPlus.Open.ResearchFormalization.BatchR0800Claims

open scoped BigOperators
open Polynomial

noncomputable section

private abbrev Coeff := MvPolynomial ℕ ℤ
private abbrev MarkerPoly := Polynomial Coeff

private def markerExpansion (polynomial : MarkerPoly) : Coeff :=
  ∑ degree ∈ polynomial.support,
    MvPolynomial.X degree * polynomial.coeff degree

private def markerDerivative (polynomial : MarkerPoly) : Coeff :=
  MvPolynomial.pderiv 1 (markerExpansion (Polynomial.X * polynomial))

private def singletonPad (u : ℕ) (polynomial : MarkerPoly) : MarkerPoly :=
  Polynomial.C (MvPolynomial.X 1 ^ u) * polynomial

private def cAxis : MarkerPoly :=
  Polynomial.X ^ 4 * Polynomial.C (MvPolynomial.X 1 ^ 3) -
    Polynomial.X * Polynomial.C (MvPolynomial.X 4 * MvPolynomial.X 1 ^ 2)

private def dAxis : MarkerPoly :=
  Polynomial.X ^ 3 * Polynomial.C (MvPolynomial.X 2 * MvPolynomial.X 1 ^ 2) -
    Polynomial.X * Polynomial.C (MvPolynomial.X 3 * MvPolynomial.X 2 * MvPolynomial.X 1)

private def eAxis : MarkerPoly :=
  Polynomial.X ^ 2 * Polynomial.C (MvPolynomial.X 3 * MvPolynomial.X 1 ^ 2) -
    Polynomial.X * Polynomial.C (MvPolynomial.X 3 * MvPolynomial.X 2 * MvPolynomial.X 1)

private def fAxis : MarkerPoly :=
  Polynomial.X ^ 2 * Polynomial.C (MvPolynomial.X 2 ^ 2 * MvPolynomial.X 1) -
    Polynomial.X * Polynomial.C (MvPolynomial.X 2 ^ 3)

/-- Claim 24844: the exact derivative image of the C₄ axis in the reviewed
marker-polynomial/MvPolynomial carrier. -/
def claim24844_imageOfC4Axis : Prop :=
  ∀ u : ℕ,
    markerDerivative (singletonPad u cAxis) =
      (u + 3 : ℤ) • (MvPolynomial.X 5 * MvPolynomial.X 1 ^ (u + 2)) -
        (u + 2 : ℤ) •
          (MvPolynomial.X 4 * MvPolynomial.X 2 * MvPolynomial.X 1 ^ (u + 1))

/-- Claim 24845: the exact derivative image of the D₄ axis. -/
def claim24845_imageOfD4Axis : Prop :=
  ∀ u : ℕ,
    markerDerivative (singletonPad u dAxis) =
      (u + 2 : ℤ) •
          (MvPolynomial.X 4 * MvPolynomial.X 2 * MvPolynomial.X 1 ^ (u + 1)) -
        (u + 1 : ℤ) •
          (MvPolynomial.X 3 * MvPolynomial.X 2 ^ 2 * MvPolynomial.X 1 ^ u)

/-- Claim 24847: the exact derivative image of the F₄ axis, with the final
negative-power term absent at u=0 rather than represented by a guessed shift. -/
def claim24847_imageOfF4Axis : Prop :=
  ∀ u : ℕ,
    markerDerivative (singletonPad u fAxis) =
      if u = 0 then
        (u + 1 : ℤ) •
          (MvPolynomial.X 3 * MvPolynomial.X 2 ^ 2 * MvPolynomial.X 1 ^ u)
      else
        (u + 1 : ℤ) •
            (MvPolynomial.X 3 * MvPolynomial.X 2 ^ 2 * MvPolynomial.X 1 ^ u) -
          (u : ℤ) •
            (MvPolynomial.X 2 ^ 4 * MvPolynomial.X 1 ^ (u - 1))

end

end MathlibPlus.Open.ResearchFormalization.BatchR0800Claims
