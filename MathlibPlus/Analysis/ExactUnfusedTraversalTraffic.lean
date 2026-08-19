import Mathlib

namespace MathlibPlus.Analysis

/-- The exact nominal byte count for two unfused 26-stage traversals at
    length `2^26`. -/
def exactUnfusedTraversalTraffic_42732 : Prop :=
  2 * 26 * 40 * 2 ^ 26 = 139586437120

end MathlibPlus.Analysis
