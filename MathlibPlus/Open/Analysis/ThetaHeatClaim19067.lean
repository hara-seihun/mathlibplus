import MathlibPlus.Analysis.ThetaShellSummandClaim19068

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim19067

noncomputable section

/-- The literal positive-half-line theta source in Claim 19067. -/
def literalPhi : ℝ → ℝ := fun u ↦
  ∑' m : {m : ℕ // 0 < m},
    MathlibPlus.Analysis.thetaShellSummand m.1 u

/-- The displayed positive-time transform, with its half-line carrier fixed. -/
def literalHeatTransform (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ici (0 : ℝ),
    Complex.exp (((t * u ^ 2 : ℝ) : ℂ)) *
      (literalPhi u : ℂ) * Complex.cos (z * (u : ℂ))

/-- Standard growth predicates for an entire function of exact order one,
using powers of the radius rather than exponential type. -/
def realEntireOrderOne (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧
    (∀ x : ℝ, (F (x : ℂ)).im = 0) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ z : ℂ,
          ‖F z‖ ≤ C * Real.exp (Real.rpow ‖z‖ (1 + ε))) ∧
    (∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 →
      ∀ C : ℝ, 0 < C →
        ∃ z : ℂ,
          C * Real.exp (Real.rpow ‖z‖ ρ) < ‖F z‖)

/-- Claim 19067: for every real time the literal transform is even, real
entire of order one, and satisfies the backward heat equation. -/
def literalPositiveTimeTransform_claim19067 : Prop :=
  ∀ t : ℝ,
    Function.Even (literalHeatTransform t) ∧
      realEntireOrderOne (literalHeatTransform t) ∧
      ∀ z : ℂ,
        HasDerivAt
          (fun s : ℝ => literalHeatTransform s z)
          (-deriv (fun w : ℂ => deriv (literalHeatTransform t) w) z) t

end

end MathlibPlus.Open.Analysis.Claim19067
