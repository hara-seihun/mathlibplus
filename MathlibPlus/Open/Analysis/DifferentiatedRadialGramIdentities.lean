import Mathlib

open scoped InnerProductSpace

namespace MathlibPlus.Open.Analysis

/-- Differentiated radial Gram identities for a positive `C²` radial kernel. -/
def differentiatedRadialGramIdentities : Prop :=
  ∀ (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (U : Set E) (Ψ : E → F) (G : ℝ → ℝ),
    IsOpen U →
    ContDiff ℝ 2 G →
    (∀ x ∈ U, DifferentiableAt ℝ Ψ x) →
    (∀ f ∈ U, ∀ g ∈ U, 0 < G (⟪f, g⟫_ℝ)) →
    (∀ f ∈ U, ∀ g ∈ U,
      ⟪Ψ f, Ψ g⟫_ℝ = G (⟪f, g⟫_ℝ)) →
    ∀ f ∈ U, ∀ g ∈ U, ∀ p q : E,
      (⟪Ψ f, fderiv ℝ Ψ g q⟫_ℝ =
          deriv G (⟪f, g⟫_ℝ) * ⟪f, q⟫_ℝ) ∧
      (⟪fderiv ℝ Ψ f p, Ψ g⟫_ℝ =
          deriv G (⟪f, g⟫_ℝ) * ⟪p, g⟫_ℝ) ∧
      (⟪fderiv ℝ Ψ f p, fderiv ℝ Ψ g q⟫_ℝ =
          deriv G (⟪f, g⟫_ℝ) * ⟪p, q⟫_ℝ +
            deriv (deriv G) (⟪f, g⟫_ℝ) *
              ⟪p, g⟫_ℝ * ⟪f, q⟫_ℝ)

end MathlibPlus.Open.Analysis
