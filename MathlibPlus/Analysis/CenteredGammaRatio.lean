import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

namespace MathlibPlus.Analysis.CenteredGammaRatio

/-- Claim 18050: the centered gamma ratio, with the real `Real.rpow` convention. -/
noncomputable def normalizedCenteredGammaRatio (z : ℝ) : ℝ :=
  Real.pi ^ (-((1 / 2 : ℝ) + z) / 2) * Real.Gamma (5 / 4 + z / 2) /
    (Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (5 / 4))

/-- The ratio is normalized at the origin. -/
theorem normalizedCenteredGammaRatio_zero :
    normalizedCenteredGammaRatio 0 = 1 := by
  unfold normalizedCenteredGammaRatio
  have hpow : Real.pi ^ (-((1 / 2 : ℝ) + 0) / 2) =
      Real.pi ^ (-(1 / 4 : ℝ)) := by norm_num
  rw [hpow]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hgamma : 0 < Real.Gamma (5 / 4 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have hden : Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (5 / 4 : ℝ) ≠ 0 := by
    exact mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hpi _)) (ne_of_gt hgamma)
  simpa using div_self hden

end MathlibPlus.Analysis.CenteredGammaRatio
