import Mathlib

namespace MathlibPlus.Open.Analysis

open Polynomial
open scoped BigOperators

noncomputable section

/-- The rational value of a natural-number parameter. -/
def ratOfNat (x : ℕ) : ℚ := x

/-- Rising factorial `x (x + 1) ... (x + k - 1)`. -/
def rising (x : ℚ) (k : ℕ) : ℚ :=
  ∏ i ∈ Finset.range k, (x + ratOfNat i)

def hookA (n m : ℕ) : ℚ :=
  ratOfNat (n + 2) * ratOfNat m ^ 2
    + ratOfNat (2 * n ^ 2 + 2 * n - 1) * ratOfNat m
    + ratOfNat ((n - 1) * (n + 1) ^ 2)

def hookB (n m : ℕ) : ℚ :=
  ratOfNat (n + 1) * ratOfNat m ^ 2
    + ratOfNat (2 * n ^ 2 - n - 3) * ratOfNat m
    + ratOfNat ((n - 1) * (n - 2) * (n + 1))

def hookU (n m : ℕ) : ℚ :=
  ratOfNat (m + 2 * n) * rising (ratOfNat (m + 1)) (n - 1)
    / ratOfNat (Nat.factorial n)

/-- The explicit quadratic correction from the admitted recurrence. -/
def hookCorrection (n m : ℕ) : Polynomial ℚ :=
  C (4 * hookU n m) * X ^ 2
    + C (2 * ratOfNat (m + 2 * n) * rising (ratOfNat (m + 1)) (n - 2)
        * hookA n m / (ratOfNat (n + 1) * ratOfNat (Nat.factorial n))) * X
    + C (ratOfNat (m + 2 * n) * ratOfNat (m + n + 1)
        * rising (ratOfNat (m + 1)) (n - 2) * hookB n m
        / (2 * ratOfNat (n + 1) * ratOfNat (Nat.factorial n)))

/-- The stable `S₃` base polynomial from the admitted statement. -/
def stableBase (m : ℕ) : Polynomial ℚ :=
  C 64 * X ^ 5
    + C (64 * (2 * ratOfNat m + 9)) * X ^ 4
    + C (4 * (27 * ratOfNat m ^ 2 + 241 * ratOfNat m + 526)) * X ^ 3
    + C (2 * (3 * ratOfNat m + 16)
        * (8 * ratOfNat m ^ 2 + 65 * ratOfNat m + 129)) * X ^ 2
    + C ((137 * ratOfNat m ^ 4 + 2498 * ratOfNat m ^ 3 + 16891 * ratOfNat m ^ 2
        + 50242 * ratOfNat m + 55728) / 12) * X
    + C ((ratOfNat m + 4) * (ratOfNat m + 6)
        * (7 * ratOfNat m ^ 3 + 94 * ratOfNat m ^ 2 + 413 * ratOfNat m + 614) / 6)

/-- Cleared second-strip polynomials, with the admitted `S₃` base and recurrence. -/
def clearedStripPolynomial : ℕ → ℕ → Polynomial ℚ
  | 0, _ => 0
  | 1, _ => 0
  | 2, _ => 0
  | 3, m => stableBase m
  | n + 1, m =>
      (C 2 * X + C (ratOfNat (m + 2 * (n + 1))))
          * clearedStripPolynomial n (m + 1)
        + C ((-1 : ℚ) ^ (n + 1)) * hookCorrection (n + 1) m

/-- Every cleared strip polynomial has coefficientwise nonnegative rational
coefficients and is positive on the nonnegative real half-line. -/
def coefficientwisePositivityOfClearedStripPolynomials : Prop :=
  ∀ (m n : ℕ), 3 ≤ n →
    (∀ k : ℕ, 0 ≤ (clearedStripPolynomial n m).coeff k) ∧
      ∀ b : ℝ, 0 ≤ b →
        0 < Polynomial.eval₂ (algebraMap ℚ ℝ) b (clearedStripPolynomial n m)

end

end MathlibPlus.Open.Analysis
