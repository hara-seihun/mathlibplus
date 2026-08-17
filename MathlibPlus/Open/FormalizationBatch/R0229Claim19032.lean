import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.R0229Claim19032

private abbrev PositiveIndex := {n : ℕ // 1 ≤ n}

private noncomputable def localFactor
    (n : PositiveIndex) (z : ℂ) : ℂ :=
  let q : ℝ := Real.exp (-(n.1 : ℝ) ^ 2)
  let ℓ : ℝ := Real.pi / (n.1 : ℝ)
  (1 + 2 * (q : ℂ) * Complex.cosh ((ℓ : ℂ) * z) + (q : ℂ) ^ 2) /
    (1 + (q : ℂ)) ^ 2

private noncomputable def densityMatchedProduct (z : ℂ) : ℂ :=
  ∏' n : PositiveIndex, localFactor n z

private noncomputable def zeroPoint
    (n : PositiveIndex) (k ε : ℤ) : ℂ :=
  (ε : ℂ) * (n.1 : ℂ) ^ 3 / (Real.pi : ℂ) +
    (((2 * k + 1 : ℤ) : ℂ) * (n.1 : ℂ) * Complex.I)

/-- Claim 19032: the normalized infinite product has exactly the displayed
positive-index off-axis divisor, and its zero multiplicities are inherited
from the corresponding normalized local factor. -/
def claim19032_exactOffAxisDivisor : Prop :=
  (∀ z : ℂ,
    densityMatchedProduct z = 0 ↔
      ∃ n : PositiveIndex, ∃ k ε : ℤ,
        (ε = -1 ∨ ε = 1) ∧
          z = zeroPoint n k ε) ∧
  (∀ z : ℂ, densityMatchedProduct z = 0 → z.re ≠ 0) ∧
  (∀ (n : PositiveIndex) (k ε : ℤ),
    (ε = -1 ∨ ε = 1) →
      analyticOrderAt densityMatchedProduct (zeroPoint n k ε) =
        analyticOrderAt (localFactor n) (zeroPoint n k ε))

end MathlibPlus.Open.FormalizationBatch.R0229Claim19032
