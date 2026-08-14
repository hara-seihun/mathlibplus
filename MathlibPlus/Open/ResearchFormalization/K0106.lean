import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.K0106

/-- Claim 8605: the local energy controls the logarithmic defect. -/
def localVariationEnergyCertificate
    (qk betaNext sk rPrev rk sNext : ℝ) : Prop :=
  let E := (sk - rPrev) ^ 2 + (rk - sNext) ^ 2
  (Real.log (qk / betaNext)) ^ 2 ≤
      (rk - sNext) ^ 2 / (rk * sNext) ∧
    (rk - sNext) ^ 2 / (rk * sNext) ≤ E / betaNext

/-- Claim 8606: the exact defect identity and its quadratic bound. -/
def exactDefectEnergyIdentityAndQuadraticBound
    (qk betaNext sk rPrev rk sNext eta : ℝ) : Prop :=
  let d := qk / betaNext - 1
  let E := (sk - rPrev) ^ 2 + (rk - sNext) ^ 2
  d ^ 2 / (1 + d) = (rk - sNext) ^ 2 / (rk * sNext) ∧
    (rk - sNext) ^ 2 / (rk * sNext) ≤ E / betaNext ∧
    (E / betaNext ≤ eta →
      (eta - Real.sqrt (eta ^ 2 + 4 * eta)) / 2 ≤ d ∧
        d ≤ (eta + Real.sqrt (eta ^ 2 + 4 * eta)) / 2)

/-- Claim 8607: the variation energy and resistance length on a finite block. -/
def variationEnergyAndResistanceLength
    (A B : ℤ) (E beta : ℤ → ℝ) (V resistance : ℝ) : Prop :=
  V = (Finset.Icc A B).sum E ∧
    resistance = (Finset.Icc A B).sum (fun k => (beta (k + 1))⁻¹)

end MathlibPlus.Open.ResearchFormalization.K0106
