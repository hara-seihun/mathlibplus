import MathlibPlus.Open.Analysis.ZeroHeightShiftClassification

namespace MathlibPlus.Open.Analysis.Claim12926

/-- Claim 12926: nonnegative raw horizontal curvature of the canonical
shift-six carrier throughout the open critical strip is equivalent to RH. -/
def claim12926 : Prop :=
  RiemannHypothesis ↔ globalCarrierNonnegative 6

end MathlibPlus.Open.Analysis.Claim12926
