import Mathlib

noncomputable section

namespace MathlibPlus.Analysis

def diagonalDifferentiation_17874 : Prop :=
  ∀ {G : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    {L : (ℝ × ℝ) →L[ℝ] ℝ},
    HasFDerivAt G L p →
      HasDerivAt
        (fun u : ℝ => G (p.1 + u, p.2 + u))
        (L (1, 0) + L (0, 1)) 0

end MathlibPlus.Analysis

end
