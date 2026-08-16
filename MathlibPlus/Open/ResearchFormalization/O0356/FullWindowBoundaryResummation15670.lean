import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0356

/-- Claim 15670: over the source's real parameters, adding the positive-order
term `pair·(truncatedExponential−1)` to the boundary-corrected zeroth channel
produces the stated full-window expression. -/
def claim15670_fullWindowBoundaryResummation : Prop :=
  ∀ (pairTerm leftBoundary rightBoundary truncatedExponential : ℝ),
    (pairTerm - leftBoundary / 2 - rightBoundary / 2) +
          pairTerm * (truncatedExponential - 1) =
      pairTerm * truncatedExponential - leftBoundary / 2 - rightBoundary / 2

end MathlibPlus.Open.ResearchFormalization.O0356
