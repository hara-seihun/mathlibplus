import Mathlib

open scoped InnerProductSpace

namespace MathlibPlus.Open.Analysis.RadialDotProductTangent

/-- Claim 13122: the natural first tangent is the Fréchet derivative in the
same feature space, for a positive radial `C²` feature identity. -/
def claim13122 : Prop :=
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
    ∀ (DΨ : E → E →L[ℝ] F),
      (∀ f ∈ U, HasFDerivAt Ψ (DΨ f) f) →
      ∀ f ∈ U, ∀ p : E, DΨ f p = (fderiv ℝ Ψ f) p

end MathlibPlus.Open.Analysis.RadialDotProductTangent
