import MathlibPlus.Open.Analysis.PrimeScoreBatch

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Claim 1204: the exact same-range threshold at the published 1.149 row.
The decimal is retained as the displayed half-open rational enclosure. -/
def exactSameRangeCoefficientThreshold_claim1204 : Prop :=
  let x₀ : ℝ := 42575222481
  let aStar : ℝ := B x₀
  let displayedLower : ℝ :=
    (11490003091852194519030898606008869 : ℝ) / (10 : ℝ) ^ (34 : ℕ)
  let displayedUpper : ℝ :=
    (11490003091852194519030898606008870 : ℝ) / (10 : ℝ) ^ (34 : ℕ)
  displayedLower ≤ aStar ∧
    aStar < displayedUpper ∧
    (∀ x : ℝ, x₀ ≤ x →
      (primeCountingReal x : ℝ) ≤ x / D aStar x ∧
        ((primeCountingReal x : ℝ) = x / D aStar x ↔ x = x₀)) ∧
    (∀ x : ℝ, x₀ < x → B x < aStar) ∧
    (∀ c : ℝ, 0 < c → D c x₀ > 0 →
      ((∀ x : ℝ, x₀ ≤ x →
          (primeCountingReal x : ℝ) < x / D c x) ↔ aStar < c))

end

end MathlibPlus.Open.Analysis
