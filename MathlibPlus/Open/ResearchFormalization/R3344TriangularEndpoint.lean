import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3344TriangularEndpoint

noncomputable section

/-- Claim 45356: the exact perturbation of the triangular quadratic has the
uniform finite-window error bound. -/
def triangularEndpointFiniteWindow_claim45356 : Prop :=
  ∀ (R ε η : ℝ),
    0 ≤ R → 0 ≤ ε → 8 * R ^ 2 * ε < η →
      let q₀ : ℝ × ℝ → ℝ := fun z =>
        z.1 ^ 2 + z.2 ^ 2 + z.1 * z.2
      let qε : ℝ × ℝ → ℝ := fun z =>
        z.1 ^ 2 + z.2 ^ 2 + (1 + 2 * ε) * z.1 * z.2
      (∀ a b : ℝ, q₀ (a, b) = a ^ 2 + b ^ 2 + a * b) ∧
      (∀ a b : ℝ,
        |qε (a, b) - q₀ (a, b)| = 2 * ε * |a * b|) ∧
      (∀ a b : ℝ, |a| ≤ 2 * R → |b| ≤ 2 * R →
        |qε (a, b) - q₀ (a, b)| ≤ 8 * R ^ 2 * ε ∧
        |qε (a, b) - q₀ (a, b)| < η)

end

end MathlibPlus.Open.ResearchFormalization.R3344TriangularEndpoint
