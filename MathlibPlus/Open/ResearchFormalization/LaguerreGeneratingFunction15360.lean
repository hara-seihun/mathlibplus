import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.LaguerreGeneratingFunction15360

noncomputable section

/-- The parameter-two generalized Laguerre polynomial in the admitted
coefficient normalization. -/
def laguerreTwo (d : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (d + 1),
    (-1 : ℝ) ^ k * (Nat.choose (d + 2) (k + 2) : ℝ) * t ^ k /
      (Nat.factorial k : ℝ)

/-- Claim 15360: the generalized Laguerre generating function on the open
unit disk. -/
def generalizedLaguerreGeneratingFunction_claim15360 : Prop :=
  ∀ (t : ℝ) (z : ℂ), ‖z‖ < 1 →
    (∑' d : ℕ, (laguerreTwo d t : ℂ) * z ^ d) =
      (1 - z)⁻¹ ^ 3 * Complex.exp (-((t : ℂ) * z / (1 - z)))

end

end MathlibPlus.Open.ResearchFormalization.LaguerreGeneratingFunction15360
