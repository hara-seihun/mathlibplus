import MathlibPlus.Open.ResearchFormalization.K0046Claim7836
import MathlibPlus.Open.Analysis.DerivativeCoefficientIdentity

open MeasureTheory

namespace MathlibPlus.Open.Analysis.VirialIdentityClaim7840

/-- The exact second integration-by-parts identity on the GHS carrier. -/
def claim7840 : Prop :=
  ∀ (Q : ℝ → ℝ) (Z : ℝ) (μ : Measure ℝ)
    (p : ℕ → Polynomial ℝ) (b : ℕ → ℝ),
    MathlibPlus.Open.ResearchFormalization.K0046Claim7836.ghsDecayContext Q Z μ →
    MathlibPlus.Open.ResearchFormalization.K0046Claim7836.ghsCurvatureHypotheses Q →
    (∀ x : ℝ, HasDerivAt Q (deriv Q x) x) →
    (∀ n : ℕ, p n ≠ 0 ∧ (p n).natDegree = n) →
    (∀ i j : ℕ,
      ∫ x : ℝ, (p i).eval x * (p j).eval x ∂μ =
        if i = j then (1 : ℝ) else 0) →
    (∀ n : ℕ, 0 < n →
      ∀ x : ℝ,
        x * (p n).eval x =
          b (n + 1) * (p (n + 1)).eval x +
            b n * (p (n - 1)).eval x) →
    (∀ n : ℕ, 0 < n → 0 < b n) →
    ∀ n : ℕ, 0 < n →
      (∫ x : ℝ,
        x * deriv Q x * ((p (n - 1)).eval x) ^ 2 ∂μ =
          2 * (n : ℝ) - 1)

end MathlibPlus.Open.Analysis.VirialIdentityClaim7840
