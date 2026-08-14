import Mathlib

namespace MathlibPlus.Open.Research

noncomputable section
open scoped BigOperators

abbrev RationalPolynomial := Polynomial ℚ
abbrev RationalPolynomialFractionField := FractionRing RationalPolynomial

def polynomialVariable : RationalPolynomial := Polynomial.X

def polynomialY (d : ℕ) : RationalPolynomial :=
  2 * polynomialVariable + Polynomial.C (d : ℚ) + 1

def risingFactorialPolynomial (d ell k : ℕ) : RationalPolynomial :=
  ∏ r ∈ Finset.range k,
    (polynomialY d - Polynomial.C (ell : ℚ) + Polynomial.C (r : ℚ))

def deltaPolynomial (d n ell : ℕ) : RationalPolynomial :=
  risingFactorialPolynomial d ell (n + ell)

def riordanEntry (e t j : ℕ) : ℚ :=
  if j ≤ t then (Nat.choose (e + j) (t - j) : ℚ) else 0

def tailIndex (n ell : ℕ) (i : Fin (ell + 1)) : ℕ :=
  if i.1 < ell then i.1 + 1 else ell + n

def hookDeterminant (d n ell : ℕ) : ℚ :=
  Matrix.det (fun i j : Fin (ell + 1) =>
    riordanEntry (d - ell) (tailIndex n ell i) j.1)

def hookZ (d n ell : ℕ) : ℚ :=
  (((d + n : ℕ) : ℚ) / ((d - ell : ℕ) : ℚ)) * hookDeterminant d n ell

def gapRowIndex (n ell : ℕ) (i : Fin ell) : ℕ :=
  if i.1 < ell - 1 then i.1 + 2 else ell + n

def gapColumnIndex (j : Fin ell) : ℕ :=
  if j.1 = 0 then 0 else j.1 + 1

def firstRowGapMinor (d n ell : ℕ) : ℚ :=
  Matrix.det (fun i j : Fin ell =>
    riordanEntry (d - ell) (gapRowIndex n ell i) (gapColumnIndex j))

def polynomialToFractionField (p : RationalPolynomial) : RationalPolynomialFractionField :=
  algebraMap RationalPolynomial RationalPolynomialFractionField p

def rationalToFractionField (q : ℚ) : RationalPolynomialFractionField :=
  algebraMap ℚ RationalPolynomialFractionField q

def normalizedHookRatio (d n ell : ℕ) : RationalPolynomialFractionField :=
  rationalToFractionField (hookZ d n ell) /
    polynomialToFractionField (risingFactorialPolynomial d ell (n + ell))

def stripS (d n ell : ℕ) : RationalPolynomialFractionField :=
  ∑ j ∈ Finset.range (ell + 1),
    (-1 : RationalPolynomialFractionField) ^ j * normalizedHookRatio d n j

def stripC (d n ell : ℕ) : RationalPolynomialFractionField :=
  polynomialToFractionField (deltaPolynomial d n ell) * stripS d n ell

def stripGap (d n ell : ℕ) : RationalPolynomialFractionField :=
  polynomialToFractionField (polynomialY d - Polynomial.C (ell : ℚ)) *
      rationalToFractionField (hookZ d n (ell - 1)) -
    rationalToFractionField (hookZ d n ell)

def stripGapIdentityRight (d n ell : ℕ) : RationalPolynomialFractionField :=
  polynomialToFractionField (2 * polynomialVariable) *
      rationalToFractionField (hookZ d n (ell - 1)) +
    rationalToFractionField
      ((((d + n : ℕ) : ℚ) / ((d - ell : ℕ) : ℚ)) * firstRowGapMinor d n ell)

def coefficientwiseNonnegative (q : RationalPolynomialFractionField) : Prop :=
  ∃ p : RationalPolynomial,
    polynomialToFractionField p = q ∧ ∀ i : ℕ, 0 ≤ p.coeff i

/-- The exact strip recurrence, first-row gap identity, and coefficientwise carrier. -/
def claim1794 : Prop :=
  ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → n ≤ d →
    stripC d n 0 = rationalToFractionField (hookZ d n 0) ∧
      (∀ ell : ℕ, 1 ≤ ell → ell < d →
        stripC d n ell =
            polynomialToFractionField
              (polynomialY d - Polynomial.C (ell : ℚ)) * stripC d n (ell - 1) +
              (-1 : RationalPolynomialFractionField) ^ ell *
                rationalToFractionField (hookZ d n ell) ∧
          stripGap d n ell = stripGapIdentityRight d n ell ∧
          coefficientwiseNonnegative (stripGap d n ell)) ∧
      (∀ ell : ℕ, ell < d → coefficientwiseNonnegative (stripC d n ell))

end

end MathlibPlus.Open.Research
