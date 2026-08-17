import Mathlib
import MathlibPlus.Open.Analysis.CHJIIWeights

namespace MathlibPlus.Open.Analysis.C0101Claim1556

noncomputable section

open MathlibPlus.Open.Analysis.CHJII

/-- Claim 1556: the named CHJ source norm at the fixed k=1 endpoint, with the
source admissibility predicate and no endpoint-vanishing clause. -/
def claim1556 : Prop :=
  ∀ w : ℝ → ℝ,
    admissibleCHJIIWeight 2 w →
      chjNorm 2 w =
        (1 / (2 * Real.pi)) *
          (w 2 / 2 + w 1 +
            ∫ u in (1 : ℝ)..2, w u / u +
            ∫ u in (1 : ℝ)..2, |deriv w u| / u)

end

end MathlibPlus.Open.Analysis.C0101Claim1556
