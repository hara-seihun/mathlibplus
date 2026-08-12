import Mathlib.Analysis.SpecialFunctions.Exp

namespace MathlibPlus.Analysis.Claim19326

/-- Claim 19326: the Gaussian source family is strictly positive and even
for every positive parameter. -/
theorem gaussianSourceFamily :
    ∀ β : ℝ, 0 < β →
      let ρ : ℝ → ℝ := fun u => Real.exp (-β * u ^ 2)
      (∀ u : ℝ, 0 < ρ u) ∧ ∀ u : ℝ, ρ (-u) = ρ u := by
  intro β _hβ
  dsimp
  constructor
  · intro u
    exact Real.exp_pos _
  · intro u
    rw [neg_sq]

end MathlibPlus.Analysis.Claim19326
