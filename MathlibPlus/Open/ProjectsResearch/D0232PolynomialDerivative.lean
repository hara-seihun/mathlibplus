import Mathlib

open Polynomial
noncomputable section

namespace MathlibPlus.Open.ProjectsResearch.D0232

/-- The sixth-row discrepancy written in the coefficient ring consisting of the
variables other than the distinguished marked variable `x₁`. -/
noncomputable def markedSixthDifference : MvPolynomial (Fin 3) ℤ :=
  MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 * MvPolynomial.X 2

/-- Claim 6683: a polynomial independent of the distinguished variable is
annihilated by differentiation in that variable, including the displayed
sixth-row discrepancy `x₃²-x₂x₄`.  A polynomial in the remaining variables is
represented as a constant polynomial over the distinguished-variable ring. -/
def derivativeBlindnessToMarkedVariable : Prop :=
  (∀ (R : Type*) [CommRing R] (P : R[X]),
    Polynomial.derivative (Polynomial.C P) = 0) ∧
  Polynomial.derivative (Polynomial.C markedSixthDifference) = 0

end MathlibPlus.Open.ProjectsResearch.D0232
