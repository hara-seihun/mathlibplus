import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The prime-counting function on real arguments, by counting primes up to the
natural floor of the argument. -/
def primeCountingReal (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ)

/-- Axler's score at a positive real argument. -/
def axlerScore (x : ℝ) : ℝ :=
  Real.log x * (Real.log x - 1 - x / primeCountingReal x)

/-- The denominator in the coefficient form of the bound. -/
def coefficientDenominator (c x : ℝ) : ℝ :=
  Real.log x - 1 - c / Real.log x

def publishedStart : ℕ := 42575222481

def repairedCoefficient : ℝ := (114900031 : ℝ) / 100000000

def coefficientThreshold : ℝ := axlerScore (publishedStart : ℝ)

def validIntegerStart (n : ℕ) : Prop :=
  ∀ x : ℝ, (n : ℝ) ≤ x →
    primeCountingReal x < x / coefficientDenominator repairedCoefficient x

/--
The exact-coefficient repair at the published start, including the least-start
claim and both displayed numerical margins.
-/
def strictCoefficientRepairAtPublishedStart : Prop :=
  (∀ x : ℝ, (publishedStart : ℝ) ≤ x →
    primeCountingReal x <
      x / coefficientDenominator repairedCoefficient x) ∧
  IsLeast {n : ℕ | validIntegerStart n} publishedStart ∧
  ((81478054809691 : ℝ) / 100000000000000000000000 ≤
      repairedCoefficient - coefficientThreshold ∧
    repairedCoefficient - coefficientThreshold <
      (81478054809692 : ℝ) / 100000000000000000000000 ∧
    0 < repairedCoefficient - coefficientThreshold) ∧
  axlerScore ((publishedStart : ℝ) - 1) - repairedCoefficient >
    (12076708182 : ℝ) / 1000000000000000000

end

end MathlibPlus.Open.Analysis
