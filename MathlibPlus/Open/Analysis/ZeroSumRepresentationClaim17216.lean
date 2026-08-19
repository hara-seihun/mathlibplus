import MathlibPlus.NumberTheory.CompletedZetaRadial

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.ZeroSumRepresentationClaim17216

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

/-- Under RH, the canonical Xi criterion function has the positive-zero
resolvent representation with analytic zero multiplicities. -/
def zeroSumRepresentationUnderRH_claim17216 (γ : ℕ → ℝ) : Prop :=
  positiveXiZeroEnumeration γ →
    riemannHypothesisForXi →
      ∀ x : ℝ, 0 < x →
        Summable (fun n : ℕ => 2 * x / (x + γ n ^ 2)) ∧
          xiCriterionFunction x =
            ∑' n : ℕ, 2 * x / (x + γ n ^ 2)

end

end MathlibPlus.Open.Analysis.ZeroSumRepresentationClaim17216
