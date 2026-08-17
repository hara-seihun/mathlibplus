import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0121

noncomputable section

private def backwardOrbitCellIntegral (n : ℕ+) (k : ℕ) : ℝ :=
  ∫ x in (n : ℝ)..((n : ℝ) + 1),
    (x - (n : ℝ)) * x ^ ((-3 : ℝ) / 2 - 2 * (k : ℝ))

/-- Claim 18095: the gamma-removed cell moments have the stated alternating
strict determinant sign on every positive-rank ordered family of positive
spectral cells and natural backward indices. -/
noncomputable def spectralBandOscillationDeterminant_18095 : Prop :=
  ∀ (r : ℕ), 0 < r →
    ∀ (n : Fin r → ℕ+) (k : Fin r → ℕ),
      StrictMono n → StrictMono k →
        (-1 : ℝ) ^ (r * (r - 1) / 2) *
            Matrix.det (fun i j : Fin r =>
              backwardOrbitCellIntegral (n i) (k j)) > 0

end

end MathlibPlus.Open.ResearchFormalization.R0121
