import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0226.Repair

noncomputable section

private def zetaRatio (w : ℂ) : ℂ :=
  riemannZeta (w - 1) / riemannZeta w

private def shiftedLogDerivativeTerm (w : ℂ)
    (k : {k : ℕ // 1 ≤ k}) : ℂ :=
  deriv zetaRatio (w + (k.1 : ℂ)) /
    zetaRatio (w + (k.1 : ℂ))

private def completedLogDerivative (w : ℂ) : ℂ :=
  ∑' k : {k : ℕ // 1 ≤ k}, shiftedLogDerivativeTerm w k

/-- The completed shifted zeta-ratio logarithmic derivative is the convergent
positive-shift telescope on the right half-plane. -/
def convergentLogDerivativeTelescope_claim19000 : Prop :=
  ∀ w : ℂ, 1 < w.re →
    Summable (shiftedLogDerivativeTerm w) ∧
      completedLogDerivative w =
        ∑' k : {k : ℕ // 1 ≤ k}, shiftedLogDerivativeTerm w k

end

end MathlibPlus.Open.NewResearch2.R0226.Repair
