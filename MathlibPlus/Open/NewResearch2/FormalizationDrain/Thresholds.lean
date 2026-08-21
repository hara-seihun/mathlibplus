import Mathlib

/-!
Formalization-drain statements for the finite threshold computations.
-/

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.NewResearch2.FormalizationDrain.Thresholds

noncomputable section

private def largestPositiveRoot
    (C : ℕ → Polynomial ℝ) (Q : ℕ → ℝ) (r : ℕ) : Prop :=
  0 < Q r ∧
    (C r).eval (Q r) = 0 ∧
    ∀ y : ℝ, 0 < y → (C r).eval y = 0 → y ≤ Q r

private def positiveOnRay
    (C : ℕ → Polynomial ℝ) (r : ℕ) (b : ℝ) : Prop :=
  ∀ q : ℝ, b ≤ q → 0 < (C r).eval q

private def shiftedThresholdPolynomial
    (C : ℕ → Polynomial ℝ) (r : ℕ) : Polynomial ℝ :=
  (C r).comp (Polynomial.C ((7 : ℝ) * (r : ℝ) / 4) + Polynomial.X)

private def allNonzeroCoefficientsPositive (p : Polynomial ℝ) : Prop :=
  ∀ k : ℕ, k ≤ p.natDegree → 0 < p.coeff k

private def displayedThresholdInterval (r : ℕ) (q : ℝ) : Prop :=
  (r = 2 ∧ q = 7 / 4) ∨
  (r = 3 ∧ (35270746093 : ℝ) / 10 ^ 10 ≤ q ∧ q < 35270746094 / 10 ^ 10) ∨
  (r = 4 ∧ (53611335998 : ℝ) / 10 ^ 10 ≤ q ∧ q < 53611335999 / 10 ^ 10) ∨
  (r = 5 ∧ (72276450550 : ℝ) / 10 ^ 10 ≤ q ∧ q < 72276450551 / 10 ^ 10) ∨
  (r = 6 ∧ (911518 : ℝ) / 10 ^ 5 ≤ q ∧ q < 911519 / 10 ^ 5) ∨
  (r = 7 ∧ (1101753 : ℝ) / 10 ^ 5 ≤ q ∧ q < 1101754 / 10 ^ 5) ∨
  (r = 8 ∧ (1293093 : ℝ) / 10 ^ 5 ≤ q ∧ q < 1293094 / 10 ^ 5) ∨
  (r = 10 ∧ (1678176 : ℝ) / 10 ^ 5 ≤ q ∧ q < 1678177 / 10 ^ 5)

/-- Claim 18206: the reported finite threshold values, with the displayed
finite decimals represented by exact rational isolating intervals. -/
def claim18206_computedFiniteThresholdValues
    (C : ℕ → Polynomial ℝ) (Q : ℕ → ℝ) : Prop :=
  (∀ r : ℕ, r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 10 →
      largestPositiveRoot C Q r ∧ displayedThresholdInterval r (Q r)) ∧
    Q 2 = (7 : ℝ) / 4 ∧
    (35270746093 : ℝ) / (10 : ℝ) ^ 10 ≤ Q 3 ∧
      Q 3 < (35270746094 : ℝ) / (10 : ℝ) ^ 10 ∧
    (53611335998 : ℝ) / (10 : ℝ) ^ 10 ≤ Q 4 ∧
      Q 4 < (53611335999 : ℝ) / (10 : ℝ) ^ 10 ∧
    (72276450550 : ℝ) / (10 : ℝ) ^ 10 ≤ Q 5 ∧
      Q 5 < (72276450551 : ℝ) / (10 : ℝ) ^ 10 ∧
    (911518 : ℝ) / (10 : ℝ) ^ 5 ≤ Q 6 ∧
      Q 6 < (911519 : ℝ) / (10 : ℝ) ^ 5 ∧
    (1101753 : ℝ) / (10 : ℝ) ^ 5 ≤ Q 7 ∧
      Q 7 < (1101754 : ℝ) / (10 : ℝ) ^ 5 ∧
    (1293093 : ℝ) / (10 : ℝ) ^ 5 ≤ Q 8 ∧
      Q 8 < (1293094 : ℝ) / (10 : ℝ) ^ 5 ∧
    (1678176 : ℝ) / (10 : ℝ) ^ 5 ≤ Q 10 ∧
      Q 10 < (1678177 : ℝ) / (10 : ℝ) ^ 5

/-- Claim 18207: rank eight is the first threshold above `4 * π`. -/
def claim18207_rankEightFirstAboveFourPi (Q : ℕ → ℝ) : Prop :=
  (∀ r : ℕ, 2 ≤ r → r < 8 → Q r ≤ 4 * Real.pi) ∧
    4 * Real.pi < Q 8

/-- Claim 18208: all coefficients through rank thirteen are strictly
positive after the stated linear shift. -/
def claim18208_shiftedCoefficientPositivityThroughThirteen
    (C : ℕ → Polynomial ℝ) : Prop :=
  ∀ r : ℕ, 2 ≤ r → r ≤ 13 →
    (∀ k : ℕ, k ≤ (shiftedThresholdPolynomial C r).natDegree →
      0 < (shiftedThresholdPolynomial C r).coeff k)

/-- Claim 18209: shifted coefficient positivity gives positivity on the
right-hand ray and places the largest positive root below the shift. -/
def claim18209_linearUpperBoundOnThresholdsThroughThirteen
    (C : ℕ → Polynomial ℝ) (Q : ℕ → ℝ) : Prop :=
  (∀ r : ℕ, 2 ≤ r → r ≤ 13 →
      largestPositiveRoot C Q r ∧
        (∀ k : ℕ, k ≤ (shiftedThresholdPolynomial C r).natDegree →
          0 < (shiftedThresholdPolynomial C r).coeff k)) →
    ∀ r : ℕ, 2 ≤ r → r ≤ 13 →
      positiveOnRay C r ((7 : ℝ) * (r : ℝ) / 4) ∧
        Q r < (7 : ℝ) * (r : ℝ) / 4

end
end MathlibPlus.Open.NewResearch2.FormalizationDrain.Thresholds
