/-!
Formalization-drain statements for the boundary layers of the polynomial
family and the square-shift coefficient transfer.
-/
import Mathlib

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.NewResearch2.FormalizationDrain.BoundaryLayers

noncomputable section

private def elementaryOne (d : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ i : Fin d, MvPolynomial.X i

private def elementaryTwo (d : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    if i < j then MvPolynomial.X i * MvPolynomial.X j else 0

private def coefficientwiseNonnegative
    {ι : Type} [DecidableEq ι]
    (p : MvPolynomial ι ℝ) : Prop :=
  ∀ m ∈ p.support, 0 ≤ p.coeff m

private def coefficientwisePositive
    {ι : Type} [DecidableEq ι]
    (p : MvPolynomial ι ℝ) : Prop :=
  ∀ m ∈ p.support, 0 < p.coeff m

private def squareShiftedSecondLayerBracket
    (d : ℕ) (c : ℝ) : MvPolynomial (Fin d) ℝ :=
  (∑ i : Fin d,
      (MvPolynomial.C (c * (((i : ℝ) + 1) ^ 2)) + MvPolynomial.X i)) -
    MvPolynomial.C ((8 * (d : ℝ) ^ 2 + 2 * (d : ℝ) - 3) / 4)

private def thirdBoundaryFactor (d : ℕ) : MvPolynomial (Fin d) ℝ :=
  elementaryOne d ^ 2 - elementaryTwo d -
      (((2 * (d : ℝ) - 1) * ((d : ℝ) + 3 / 4))) • elementaryOne d +
    (((d - 1 : ℕ) : ℝ) * (2 * (d : ℝ) - 1) *
      (48 * (d : ℝ) ^ 2 + 32 * (d : ℝ) - 5) / 48) •
      (1 : MvPolynomial (Fin d) ℝ)

/-- Claim 18218: the top boundary coefficient in the last variable. -/
def claim18218_topBoundaryLayerIdentity
    (Pd : ∀ d : ℕ, MvPolynomial (Fin d) ℝ)
    (Pnext : ∀ d : ℕ, Polynomial (MvPolynomial (Fin d) ℝ)) : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    (Pnext d).coeff d =
      ((2 : ℝ) * (Nat.factorial d : ℝ)) • Pd d

/-- Claim 18219: the second boundary coefficient in the last variable. -/
def claim18219_secondBoundaryLayerIdentity
    (Pd : ∀ d : ℕ, MvPolynomial (Fin d) ℝ)
    (Pnext : ∀ d : ℕ, Polynomial (MvPolynomial (Fin d) ℝ)) : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    (Pnext d).coeff (d - 1) =
      ((2 : ℝ) * (Nat.factorial d : ℝ)) •
        ((∑ i : Fin d, MvPolynomial.X i) -
          MvPolynomial.C ((8 * (d : ℝ) ^ 2 + 2 * (d : ℝ) - 3) / 4)) * Pd d

/-- Claim 18220: the square-shifted second-layer bracket is coefficientwise
strictly positive for every rank and shift parameter in the stated range. -/
def claim18220_squareShiftedSecondLayerBracketPositive : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ c : ℝ, 2 ≤ c →
    coefficientwisePositive (squareShiftedSecondLayerBracket d c)

/-- Claim 18221: nonnegativity at rank d transfers to both displayed boundary
layers at rank d+1 after the square shift. -/
def claim18221_topTwoBoundaryLayerPositivityTransfer : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ c : ℝ, 2 ≤ c →
    ∀ (Pd : MvPolynomial (Fin d) ℝ)
      (Pnext : Polynomial (MvPolynomial (Fin d) ℝ)),
      coefficientwiseNonnegative Pd ∧
      (Pnext.coeff d =
        ((2 : ℝ) * (Nat.factorial d : ℝ)) • Pd) ∧
      (Pnext.coeff (d - 1) =
        ((2 : ℝ) * (Nat.factorial d : ℝ)) •
          (squareShiftedSecondLayerBracket d c * Pd)) →
        coefficientwiseNonnegative (Pnext.coeff d) ∧
          coefficientwiseNonnegative (Pnext.coeff (d - 1))

/-- Claim 18222: the third boundary coefficient, including the raised-column
companion term and its exact constants. -/
def claim18222_thirdBoundaryLayerIdentity
    (Pd : ∀ d : ℕ, MvPolynomial (Fin d) ℝ)
    (Pnext : ∀ d : ℕ, Polynomial (MvPolynomial (Fin d) ℝ))
    (R : ∀ d : ℕ, MvPolynomial (Fin d) ℝ) : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    (Pnext d).coeff (d - 2) =
      ((2 : ℝ) * (Nat.factorial d : ℝ)) •
          (thirdBoundaryFactor d * Pd d) -
        (((2 : ℝ) * (d - 1 : ℕ) * (Nat.factorial (d - 1) : ℝ)) • R d)

end
end MathlibPlus.Open.NewResearch2.FormalizationDrain.BoundaryLayers
