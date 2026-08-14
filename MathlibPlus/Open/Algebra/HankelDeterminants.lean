import Mathlib

namespace MathlibPlus.Open.Algebra

open scoped BigOperators

noncomputable section

open Classical

/-- The formal polynomial ring in the power-sum variables p_j. -/
abbrev PowerSumPolynomial := MvPolynomial ℕ ℤ

/-- The formal variable p_j. -/
def powerSumVariable (j : ℕ) : PowerSumPolynomial :=
  MvPolynomial.X j

/-- The (r by r) Hankel determinant H_r. -/
def hankelEntry (r : ℕ) (i j : Fin r) : PowerSumPolynomial :=
  powerSumVariable ((i : ℕ) + (j : ℕ) + 1)

def hankelDeterminant (r : ℕ) : PowerSumPolynomial :=
  Matrix.det (fun i j : Fin r => hankelEntry r i j)

/-- The shifted (r-1 by r-1) Hankel determinant K_r. -/
def shiftedHankelDeterminant (r : ℕ) : PowerSumPolynomial :=
  Matrix.det (fun i j : Fin (r - 1) =>
    powerSumVariable ((i : ℕ) + (j : ℕ) + 3))

/-- The exponent of the diagonal monomial p_3 p_5 ... p_(2r-1). -/
def oddDiagonalExponent (r : ℕ) : ℕ →₀ ℕ :=
  ∑ i : Fin (r - 1), Finsupp.single (2 * (i : ℕ) + 3) 1

/-- A partial derivative in p_j, represented by the canonical polynomial derivation. -/
def partialPowerSumDerivative (j : ℕ) :
    PowerSumPolynomial →ₗ[ℤ] PowerSumPolynomial :=
  (MvPolynomial.mkDerivation ℤ
    (fun i : ℕ => if i = j then (1 : PowerSumPolynomial) else 0)).toLinearMap

/-- Iterated application of a polynomial endomorphism. -/
def iterateEndomorphism {α : Type} (f : α → α) : ℕ → α → α
  | 0, x => x
  | n + 1, x => iterateEndomorphism f n (f x)

def iteratedPartialPowerSumDerivative (j k : ℕ) (P : PowerSumPolynomial) :
    PowerSumPolynomial :=
  iterateEndomorphism (partialPowerSumDerivative j) k P

/-- Hankel differentiation, nonvanishing, and the explicit r=3 formulas. -/
def hankelDeterminantDerivativeAndNonvanishing : Prop :=
  (∀ r : ℕ, 3 ≤ r →
    (∀ i j : Fin r,
        (1 ∈ MvPolynomial.vars (hankelEntry r i j) ↔
          (i : ℕ) = 0 ∧ (j : ℕ) = 0)) ∧
    partialPowerSumDerivative 1 (hankelDeterminant r) =
      shiftedHankelDeterminant r ∧
    (∀ k : ℕ, 2 ≤ k →
      iteratedPartialPowerSumDerivative 1 k (hankelDeterminant r) = 0) ∧
    shiftedHankelDeterminant r ≠ 0 ∧
    MvPolynomial.coeff (oddDiagonalExponent r)
      (shiftedHankelDeterminant r) = 1) ∧
  hankelDeterminant 3 =
    powerSumVariable 1 * powerSumVariable 3 * powerSumVariable 5 -
      powerSumVariable 1 * powerSumVariable 4 ^ 2 -
      powerSumVariable 2 ^ 2 * powerSumVariable 5 +
      2 * powerSumVariable 2 * powerSumVariable 3 * powerSumVariable 4 -
      powerSumVariable 3 ^ 3 ∧
  shiftedHankelDeterminant 3 =
    powerSumVariable 3 * powerSumVariable 5 - powerSumVariable 4 ^ 2

end

end MathlibPlus.Open.Algebra
