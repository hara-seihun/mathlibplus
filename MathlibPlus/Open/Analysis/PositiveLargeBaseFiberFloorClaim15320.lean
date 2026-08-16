import MathlibPlus.Open.Analysis.LargeBaseFiberFloor

open Filter MeasureTheory

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Claim 15320: substitution of the limiting fiber moments into the exact
minimum gives a strictly positive large-base limit for the fiber floor. -/
def positiveLargeBaseFiberFloorLimitClaim15320 : Prop :=
  let calA : ℝ :=
    ∫ t, ‖criticalResidual t‖ ^ 2 ∂criticalCauchyMeasure
  Filter.Tendsto (fun q : ℕ => fiberFloor q) Filter.atTop
      (nhds (1 - 1 / calA)) ∧
    0 < 1 - 1 / calA

end

end MathlibPlus.Open.Analysis
