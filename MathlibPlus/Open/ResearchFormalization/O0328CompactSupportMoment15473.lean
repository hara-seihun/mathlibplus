import MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459
import MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers

open MeasureTheory Set Classical
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.O0328CompactSupportMoment15473

noncomputable section

/-- The positive-half-line `L¹` norm of the real source. -/
noncomputable def positiveHalfLineL1Norm (q : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Set.Ioi (0 : ℝ), |q x|

/-- Claim 15473: on the reviewed center-flat compact-source carrier, the
exact Mellin sample at `2n+1` obeys the compact-support moment bound. -/
def claim15473_compactSupportMomentBound : Prop :=
  ∀ (a R : ℝ),
    0 < a →
      a < R →
        ∀ q : ℝ → ℝ,
          q ∈
              MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459.centerFlatSourceClass a R →
            ∀ n : ℕ,
              ‖MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers.sourceMellin q (2 * (n : ℂ) + 1)‖ ≤
                positiveHalfLineL1Norm q * R ^ (2 * n)

end

end MathlibPlus.Open.ResearchFormalization.O0328CompactSupportMoment15473
