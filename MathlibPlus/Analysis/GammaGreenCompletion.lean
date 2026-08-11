import Mathlib

namespace MathlibPlus.Analysis.GammaGreenCompletion

/-- Claim 18044: the gamma/Green completion factor is positive on `(0, 1)`. -/
theorem gammaGreenCompletionFactor_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    0 < s * (1 - s) * Real.pi ^ (-s / 2) * Real.Gamma (1 + s / 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hrpow : 0 < Real.pi ^ (-s / 2) := Real.rpow_pos_of_pos hpi _
  have harg : 0 < 1 + s / 2 := by
    linarith
  have hgamma : 0 < Real.Gamma (1 + s / 2) := Real.Gamma_pos_of_pos harg
  positivity

end MathlibPlus.Analysis.GammaGreenCompletion
