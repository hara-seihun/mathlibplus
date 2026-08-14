import Mathlib
namespace MathlibPlus.Open.ResearchFormalization.BatchInterpolation

noncomputable section
open scoped BigOperators

/-- The geometric levels `α 4^(-(j-1))`, indexed from zero. -/
def geometricLevel (α : ℝ) (j : ℕ) : ℝ :=
  α * (4 : ℝ) ^ (-(j : ℤ))

/-- The endpoint interpolation weight at a zero-based level. -/
def geometricEndpointWeight (α : ℝ) (M j : ℕ) : ℝ :=
  Finset.prod ((Finset.range M).filter (fun i => i ≠ j))
    (fun i => geometricLevel α i / |geometricLevel α i - geometricLevel α j|)

/-- Claim 6007: the geometric endpoint weights have the uniform bound. -/
def geometricEndpointInterpolationWeights : Prop :=
  ∀ (α : ℝ), 0 < α → ∀ (M : ℕ), 0 < M →
    Finset.sum (Finset.range M) (geometricEndpointWeight α M) < 3

end
end MathlibPlus.Open.ResearchFormalization.BatchInterpolation
