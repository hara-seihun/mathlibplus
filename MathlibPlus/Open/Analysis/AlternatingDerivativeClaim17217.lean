import MathlibPlus.NumberTheory.CompletedZetaRadial

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.AlternatingDerivativeClaim17217

open MathlibPlus.NumberTheory.CompletedZetaRadial

noncomputable section

private noncomputable def modularXiTransform (w : ℂ) : ℂ :=
  riemannXi ((1 / 2 : ℂ) + Complex.sqrt w) / riemannXi (1 / 2 : ℂ)

private noncomputable def xiCriterionFunction (x : ℝ) : ℝ :=
  (2 * (x : ℂ) * deriv modularXiTransform (x : ℂ) /
      modularXiTransform (x : ℂ)).re

private def riemannHypothesisForXi : Prop :=
  ∀ ρ : ℂ, riemannXi ρ = 0 → ρ.re = 1 / 2

private def positiveXiZeroEnumeration (γ : ℕ → ℝ) : Prop :=
  (∀ n : ℕ,
    0 < γ n ∧
      riemannXi ((1 / 2 : ℂ) + (γ n : ℂ) * Complex.I) = 0) ∧
    ∀ t : ℝ, 0 < t →
      (Set.Finite {n : ℕ | γ n = t} ∧
        Set.ncard {n : ℕ | γ n = t} =
          analyticOrderNatAt riemannXi
            ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) ∧
      (riemannXi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0 ↔
        ∃ n : ℕ, γ n = t)

/-- Claim 17217: under RH, the derivatives of the canonical Xi criterion
function have the displayed alternating formula and are strictly positive
in the corresponding sign. -/
def alternatingDerivativeFormula_claim17217 (γ : ℕ → ℝ) : Prop :=
  positiveXiZeroEnumeration γ →
    riemannHypothesisForXi →
      ∀ (n : ℕ) (x : ℝ), 1 ≤ n → 0 < x →
        ((-1 : ℝ) ^ (n - 1) *
            iteratedDeriv n xiCriterionFunction x =
          2 * (Nat.factorial n : ℝ) *
            ∑' k : ℕ,
              γ k ^ 2 / (x + γ k ^ 2) ^ (n + 1)) ∧
        0 < 2 * (Nat.factorial n : ℝ) *
          ∑' k : ℕ,
            γ k ^ 2 / (x + γ k ^ 2) ^ (n + 1)

end

end MathlibPlus.Open.Analysis.AlternatingDerivativeClaim17217
