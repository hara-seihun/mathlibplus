import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0800

noncomputable section

open Classical
open scoped BigOperators

abbrev MarkerCoefficient := MvPolynomial ℕ ℤ
abbrev MarkerPolynomial := Polynomial MarkerCoefficient

private def markerVariable : MarkerPolynomial := Polynomial.X

/-- The marker-to-component-size expansion used by the reviewed derivative
carrier for R-0800. -/
def markerExpansion (p : MarkerPolynomial) : MarkerCoefficient :=
  ∑ n ∈ p.support,
    MvPolynomial.X n * p.coeff n

/-- `L(H)=∂_{x₁} Φ(zH)` on the common marker-polynomial carrier. -/
def defectFourOperator (H : MarkerPolynomial) : MarkerCoefficient :=
  MvPolynomial.pderiv 1 (markerExpansion (markerVariable * H))

/-- The four universal defect-four axes. -/
def axisC4 : MarkerPolynomial :=
  markerVariable ^ 4 * Polynomial.C (MvPolynomial.X 1 ^ 3) -
    markerVariable * Polynomial.C (MvPolynomial.X 4 * MvPolynomial.X 1 ^ 2)

def axisD4 : MarkerPolynomial :=
  markerVariable ^ 3 * Polynomial.C (MvPolynomial.X 2 * MvPolynomial.X 1 ^ 2) -
    markerVariable * Polynomial.C (MvPolynomial.X 3 * MvPolynomial.X 2 * MvPolynomial.X 1)

def axisE4 : MarkerPolynomial :=
  markerVariable ^ 2 * Polynomial.C (MvPolynomial.X 3 * MvPolynomial.X 1 ^ 2) -
    markerVariable * Polynomial.C (MvPolynomial.X 3 * MvPolynomial.X 2 * MvPolynomial.X 1)

def axisF4 : MarkerPolynomial :=
  markerVariable ^ 2 * Polynomial.C (MvPolynomial.X 2 ^ 2 * MvPolynomial.X 1) -
    markerVariable * Polynomial.C (MvPolynomial.X 2 ^ 3)

/-- Multiplication by the singleton-padding factor `x₁^u`. -/
def singletonPad (u : ℕ) (H : MarkerPolynomial) : MarkerPolynomial :=
  Polynomial.C (MvPolynomial.X 1 ^ u) * H

/-- Membership in `x₁^u span {C₄,D₄,E₄,F₄}`, with the four scalar
coefficients retained explicitly over the reviewed integer coefficient ring. -/
def inPaddedDefectFourSpan (u : ℕ) (H : MarkerPolynomial) : Prop :=
  ∃ a b c d : ℤ,
    H = a • singletonPad u axisC4 +
      b • singletonPad u axisD4 +
      c • singletonPad u axisE4 +
      d • singletonPad u axisF4

/-- Claim 24848: the derivative operator is injective on the complete
padded defect-four span. -/
def claim24848_injectiveOnEntireDefectFourSpan : Prop :=
  ∀ (u : ℕ) (P Q : MarkerPolynomial),
    inPaddedDefectFourSpan u P →
    inPaddedDefectFourSpan u Q →
    defectFourOperator P = defectFourOperator Q →
    P = Q

end
end MathlibPlus.Open.ResearchFormalization.R0800
