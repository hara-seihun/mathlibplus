import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Faithful numerical registry node for the 2,049-point hotspot report.  The
sampled second-derivative values are kept as an explicit finite sample
function; the packet does not define the underlying current or gap. -/
def oneSidedCurrentCurvatureScalarizationFails_claim21439 : Prop :=
  ∃ (sampledLogAbsJSecond : Fin 2049 → ℝ)
    (sampleMaximum curvatureBound terminalBudget : ℝ),
    (∀ x, sampledLogAbsJSecond x ≤ sampleMaximum) ∧
    (∃ x, sampledLogAbsJSecond x = sampleMaximum) ∧
    |sampleMaximum -
        (23245161803248266 : ℝ) / 1000000000000000| ≤
      (1 : ℝ) / 10 ^ 15 ∧
    |curvatureBound -
        (22263075903341245 : ℝ) / 10000000000000000| ≤
      (1 : ℝ) / 10 ^ 16 ∧
    |terminalBudget -
        (536205532314541 : ℝ) / 1000000000000000| ≤
      (1 : ℝ) / 10 ^ 15 ∧
    curvatureBound > terminalBudget

end MathlibPlus.Open.Analysis

namespace MathlibPlus.Analysis.Claim21439

/-- The displayed curvature bound is strictly above the displayed terminal
budget, independently of the omitted sampling semantics. -/
theorem curvatureBound_gt_terminalBudget_claim21439 :
    (22263075903341245 : ℝ) / 10000000000000000 >
      (536205532314541 : ℝ) / 1000000000000000 := by
  norm_num

end MathlibPlus.Analysis.Claim21439
