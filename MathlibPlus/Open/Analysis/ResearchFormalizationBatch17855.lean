import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 17855: exact central logarithmic derivative of the gamma–Green factor. -/
def claim_17855 : Prop :=
  let q : ℝ → ℝ := fun s =>
    s * (1 - s) * Real.pi ^ (-s / 2) * Real.Gamma (1 + s / 2)
  let psi : ℝ → ℝ := fun s =>
    deriv (fun t : ℝ => Real.Gamma t) s / Real.Gamma s
  let value : ℝ :=
    deriv q (1 / 2) / q (1 / 2)
  (value = (1 / 2) * (psi (5 / 4) - Real.log Real.pi)) ∧
    (value = 2 - Real.eulerMascheroniConstant / 2 - Real.pi / 4 -
      (3 / 2) * Real.log 2 - (1 / 2) * Real.log Real.pi) ∧
    value < 0

end MathlibPlus.Open.Analysis
