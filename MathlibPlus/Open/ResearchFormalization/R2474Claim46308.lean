import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2474Claim46308

/-- Claim 46308's exact logarithmic discrepancy.  Endpoint numerical margins
and the inherited route inequality are source interfaces, not silently
reconstructed here. -/
def kappaPrinted_sub_kappaLegal_claim46308 : Prop :=
  ∀ (c t sigma : ℝ),
    let x : ℝ := Real.log t
    let L : ℝ := Real.log x
    let lambdaStar : ℝ :=
      c * (Real.log (Real.log t) / Real.log t) ^ (2 / 3 : ℝ)
    let r : ℝ := (1 - sigma) / lambdaStar
    let kappaLegal : ℝ :=
      (1 / 3 : ℝ) * Real.log L +
        (1 / 2 : ℝ) * Real.log c +
        (1 / 2 : ℝ) * Real.log (1 - r)
    let kappaPrinted : ℝ :=
      (1 / 3 : ℝ) * Real.log L -
        (1 / 3 : ℝ) * Real.log c +
        (1 / 2 : ℝ) * Real.log (1 - r)
    kappaPrinted - kappaLegal = -(5 / 6 : ℝ) * Real.log c

end MathlibPlus.Open.ResearchFormalization.R2474Claim46308
