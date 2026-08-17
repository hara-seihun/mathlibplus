import Mathlib.NumberTheory.PrimeCounting

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Claim1319

def primeCountReal (x : ℝ) : ℝ :=
  (Nat.primeCounting ⌊x⌋₊ : ℝ)

def axlerScore (x : ℝ) : ℝ :=
  Real.log x * (Real.log x - 1 - x / primeCountReal x)

def denominator (c x : ℝ) : ℝ :=
  Real.log x - 1 - c / Real.log x

/-- The exact same-range threshold at the published 1.149 row. -/
def exactSameRangeCoefficientThreshold_claim1319 : Prop :=
  let x₀ : ℝ := 42575222481
  let aStar : ℝ := axlerScore x₀
  let displayedLower : ℝ :=
    11490003091852194519030898606008869 / (10 : ℝ) ^ 34
  let displayedUpper : ℝ :=
    11490003091852194519030898606008870 / (10 : ℝ) ^ 34
  (∀ x : ℝ, x₀ ≤ x →
      primeCountReal x ≤ x / denominator aStar x ∧
        (primeCountReal x = x / denominator aStar x ↔ x = x₀)) ∧
    (∀ c : ℝ, 0 < c → denominator c x₀ > 0 →
      ((∀ x : ℝ, x₀ ≤ x →
          primeCountReal x < x / denominator c x) ↔ aStar < c)) ∧
    displayedLower ≤ aStar ∧ aStar < displayedUpper

end MathlibPlus.Open.ResearchFormalization.Claim1319
