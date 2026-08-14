import Mathlib

namespace MathlibPlus.Open.Analysis

/-- If two everywhere-differentiable real functions have continuous derivative
    difference vanishing on a dense set and agree at one point, they agree
    everywhere. -/
def denseDerivativeReconstructionContinuousDifference : Prop :=
  ∀ (f g F G : ℝ → ℝ) (S : Set ℝ),
    Differentiable ℝ f →
    Differentiable ℝ g →
    (∀ x : ℝ, HasDerivAt f (F x) x) →
    (∀ x : ℝ, HasDerivAt g (G x) x) →
    Dense S →
    Continuous (fun x : ℝ => F x - G x) →
    (∀ x ∈ S, F x = G x) →
    (∃ a : ℝ, f a = g a) →
    f = g

end MathlibPlus.Open.Analysis
