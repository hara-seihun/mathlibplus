import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The coefficient at an integer index, with negative indices interpreted as zero. -/
def integerCoefficient (p : Polynomial ℤ) (n : ℤ) : ℤ :=
  if 0 ≤ n then p.coeff n.toNat else 0

/-- The rectangular Toeplitz determinant attached to a coefficient sequence. -/
def rectangularToeplitzMinor (p : Polynomial ℤ) (r k : ℕ) : ℤ :=
  Matrix.det (fun i j : Fin r =>
    integerCoefficient p ((k : ℤ) + (j.val : ℤ) - (i.val : ℤ)))

/-- The original packet polynomial and its one-factor quotient. -/
def originalPacketPolynomial : Polynomial ℤ :=
  (1 + Polynomial.X)^2 * (1 + Polynomial.X^2)

def oneFactorQuotientPolynomial : Polynomial ℤ :=
  (1 + Polynomial.X) * (1 + Polynomial.X^2)

def quotientPacketValue (r : ℕ) : ℤ :=
  if r % 4 = 0 ∨ r % 4 = 1 then 1 else 0

def completeRectangularPacketNonnegative (p : Polynomial ℤ) : Prop :=
  (∀ r : ℕ, 1 ≤ r →
    0 ≤ rectangularToeplitzMinor p r 1 ∧
    0 ≤ rectangularToeplitzMinor p r 2) ∧
  ∀ r k : ℕ, 1 ≤ r → 0 ≤ rectangularToeplitzMinor p r k

/-- The complete rectangular packet of the quotient polynomial. -/
def rectangularPacket_claim12027 : Prop :=
  (∀ r : ℕ, 1 ≤ r →
    rectangularToeplitzMinor oneFactorQuotientPolynomial r 1 =
      rectangularToeplitzMinor oneFactorQuotientPolynomial r 2 ∧
    rectangularToeplitzMinor oneFactorQuotientPolynomial r 1 =
      quotientPacketValue r) ∧
  (∀ r : ℕ, 1 ≤ r →
    rectangularToeplitzMinor oneFactorQuotientPolynomial r 3 = 1) ∧
  (∀ r k : ℕ, 1 ≤ r → 3 < k →
    rectangularToeplitzMinor oneFactorQuotientPolynomial r k = 0) ∧
  completeRectangularPacketNonnegative oneFactorQuotientPolynomial

/-- The original determinant packet has positive, zero, and negative values. -/
def undeletedOriginalPacket_claim12028 : Prop :=
  (∃ r : ℕ, 1 ≤ r ∧
    0 < rectangularToeplitzMinor originalPacketPolynomial r 2) ∧
  (∃ r : ℕ, 1 ≤ r ∧
    rectangularToeplitzMinor originalPacketPolynomial r 2 = 0) ∧
  (∃ r : ℕ, 1 ≤ r ∧
    rectangularToeplitzMinor originalPacketPolynomial r 2 < 0) ∧
  Set.Infinite {r : ℕ |
    1 ≤ r ∧ 0 < rectangularToeplitzMinor originalPacketPolynomial r 2} ∧
  Set.Infinite {r : ℕ |
    1 ≤ r ∧ rectangularToeplitzMinor originalPacketPolynomial r 2 < 0} ∧
  completeRectangularPacketNonnegative oneFactorQuotientPolynomial

def originalComplexPolynomial : Polynomial ℂ :=
  (1 + Polynomial.X)^2 * (1 + Polynomial.X^2)

def reflectedOriginalComplexPolynomial : Polynomial ℂ :=
  originalComplexPolynomial.comp (-Polynomial.X)

def hasRepeatedPositiveShell : Prop :=
  (Polynomial.X - 1)^2 ∣ reflectedOriginalComplexPolynomial ∧
  ¬ (Polynomial.X - 1)^3 ∣ reflectedOriginalComplexPolynomial

def hasRepeatedNegativeRealZero : Prop :=
  (Polynomial.X + 1)^2 ∣ originalComplexPolynomial ∧
  ¬ (Polynomial.X + 1)^3 ∣ originalComplexPolynomial

def hasNonrealOriginalZeros : Prop :=
  Polynomial.IsRoot originalComplexPolynomial Complex.I ∧
  Polynomial.IsRoot originalComplexPolynomial (-Complex.I)

def allZerosRealNonpositive (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, Polynomial.IsRoot p z → z.im = 0 ∧ z.re ≤ 0

/-- The quotient-packet counterexample with a repeated positive shell. -/
def oneZeroDeflatedPackets_claim12029 : Prop :=
  completeRectangularPacketNonnegative oneFactorQuotientPolynomial ∧
  (∀ r : ℕ, 1 ≤ r →
    0 ≤ rectangularToeplitzMinor oneFactorQuotientPolynomial r 1 ∧
    0 ≤ rectangularToeplitzMinor oneFactorQuotientPolynomial r 2) ∧
  hasRepeatedPositiveShell ∧
  hasRepeatedNegativeRealZero ∧
  hasNonrealOriginalZeros ∧
  ¬ allZerosRealNonpositive originalComplexPolynomial

end

end MathlibPlus.Open.Analysis
