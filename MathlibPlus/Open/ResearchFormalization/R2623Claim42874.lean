import MathlibPlus.Analysis.Claim42868
import MathlibPlus.Analysis.Claim42870
import MathlibPlus.Analysis.Claim42872
import MathlibPlus.Analysis.GammaOddCenters

namespace MathlibPlus.Open.ResearchFormalization.R2623Claim42874

noncomputable section

private def reflectedReference42874 : ℝ → ℝ := fun s =>
  Real.Gamma ((1 + s) / 2) * Real.cos (Real.pi * s / 2) / Real.pi

def claim42874 : Prop :=
  ∀ n : ℕ,
    reflectedReference42874 (2 * (n : ℝ) + 1) = 0 ∧
      deriv reflectedReference42874 (2 * (n : ℝ) + 1) ≠ 0

end

end MathlibPlus.Open.ResearchFormalization.R2623Claim42874
