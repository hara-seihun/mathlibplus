import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0233Claim19061

noncomputable section

open scoped BigOperators

/-- The centered multiplier of the actual finite reciprocal-scale mixture. -/
def reciprocalScaleMultiplier {ι : Type*} [Fintype ι]
    (c₀ : ℝ) (c : ι → ℝ) (a : ι → ℝ) (z : ℂ) : ℂ :=
  (c₀ : ℂ) +
    2 * ∑ i : ι,
      ((c i * Real.rpow (a i) (-1 / 4 : ℝ) : ℝ) : ℂ) *
        Complex.cosh (z * ((Real.log (a i) / 2 : ℝ) : ℂ))

/-- The exact completed-Mellin normalization `Xi(s) = Lambda(s) M(s)`. -/
def completedMellinXi {ι : Type*} [Fintype ι]
    (c₀ : ℝ) (c : ι → ℝ) (a : ι → ℝ) (s : ℂ) : ℂ :=
  completedRiemannZeta s *
    reciprocalScaleMultiplier c₀ c a (s - (1 / 2 : ℂ))

/-- Claim 19061: the exact reciprocal-scale multiplier is even in centered
coordinates, and its completed Mellin transform has the centered functional
equation in the stated normalization. -/
def claim19061 : Prop :=
  ∀ (ι : Type*) [Fintype ι]
    (c₀ : ℝ) (c : ι → ℝ) (a : ι → ℝ),
    0 < c₀ →
      (∀ i : ι, 0 ≤ c i ∧ 0 < a i) →
        (∀ z : ℂ,
          reciprocalScaleMultiplier c₀ c a z =
            reciprocalScaleMultiplier c₀ c a (-z)) ∧
          (∀ z : ℂ,
            completedMellinXi c₀ c a ((1 / 2 : ℂ) + z) =
              completedMellinXi c₀ c a ((1 / 2 : ℂ) - z))

end
end MathlibPlus.Open.ResearchFormalization.R0233Claim19061
