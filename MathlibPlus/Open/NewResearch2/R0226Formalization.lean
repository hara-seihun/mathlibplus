import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0226

noncomputable section

/-- Claim 18999: on the common domain of the convergent shifted series, the
logarithmic derivative of the zeta quotient is the difference of the same
completed logarithmic derivative at consecutive shifts. -/
def claim18999 : Prop :=
  let R : ℂ → ℂ := fun w => riemannZeta (w - 1) / riemannZeta w
  let shiftedTerm : ℂ → {k : ℕ // 1 ≤ k} → ℂ := fun w k =>
    deriv R (w + (k.1 : ℂ)) / R (w + (k.1 : ℂ))
  let completedLogDerivative : ℂ → ℂ := fun w =>
    ∑' k : {k : ℕ // 1 ≤ k}, shiftedTerm w k
  let completedLogDerivativeDefined : ℂ → Prop := fun w =>
    Summable (shiftedTerm w)
  let L_R : ℂ → ℂ := fun w => deriv R w / R w
  ∀ w : ℂ,
    completedLogDerivativeDefined (w - 1) →
      completedLogDerivativeDefined w →
      riemannZeta (w - 1) ≠ 0 →
      riemannZeta w ≠ 0 →
      (∀ k : {k : ℕ // 1 ≤ k},
        R (w - 1 + (k.1 : ℂ)) ≠ 0 ∧ R (w + (k.1 : ℂ)) ≠ 0) →
      L_R w = completedLogDerivative (w - 1) - completedLogDerivative w

end

end MathlibPlus.Open.NewResearch2.R0226
