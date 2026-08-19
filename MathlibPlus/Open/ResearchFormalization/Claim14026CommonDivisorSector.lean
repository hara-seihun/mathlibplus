import MathlibPlus.Open.ResearchFormalization.BatchR2625Claim42891

namespace MathlibPlus.Open.ResearchFormalization.Claim14026

open MathlibPlus.Algebra.Claim42889
open MathlibPlus.Open.ResearchFormalization.BatchR2625Claim42891

noncomputable section

/-- The exact common-gcd `d = 2` contribution of the reviewed Gaussian-shell
polarizations lies in the displayed interval and is strictly negative. -/
def commonDivisorSectorD2Negative_claim14026 : Prop :=
  ∃ (B₂ : Polarization 2) (B₃ : Polarization 3) (B₄ : Polarization 4),
    uniquePolarization B₂ determinantPiece₂ ∧
    uniquePolarization B₃ determinantPiece₃ ∧
    uniquePolarization B₄ determinantPiece₄ ∧
    let E₂ := totalGcdShellContribution B₂ B₃ B₄ 2
    |E₂ - (-(37566625395900099211361416 : ℝ) / (10 : ℝ) ^ 45)| ≤
        (741 : ℝ) / (10 : ℝ) ^ 48 ∧
      E₂ < 0

end

end MathlibPlus.Open.ResearchFormalization.Claim14026
