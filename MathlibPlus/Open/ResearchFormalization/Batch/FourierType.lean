import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch.FourierType

noncomputable def literalTransform (L : ℝ) (κ : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Set.Icc (-L) L,
    κ t * Complex.exp (Complex.I * z * (t : ℂ))

noncomputable def literalL1Norm (L : ℝ) (κ : ℝ → ℂ) : ℝ :=
  ∫ t in Set.Icc (-L) L, ‖κ t‖

/-- Claim 3622: a compactly supported literal has exponential type at most its width. -/
def claim3622 : Prop :=
  ∀ L : ℝ, 0 ≤ L → ∀ κ : ℝ → ℂ,
    MeasureTheory.IntegrableOn κ (Set.Icc (-L) L) →
    ∀ x y : ℝ,
      ‖literalTransform L κ ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        literalL1Norm L κ * Real.exp (L * |y|)

end MathlibPlus.Open.ResearchFormalization.Batch.FourierType
