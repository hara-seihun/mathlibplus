import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The differentiated odd-packet threshold is the value threshold at the shifted exponent. -/
def claim11516_derivativePersistenceThreshold : Prop :=
  let oddPacket : ℕ → ℝ → ℝ := fun M q =>
    (((1 - q) ^ M)⁻¹ - ((1 + q) ^ M)⁻¹) / 2
  let derivativeOddPacket : ℕ → ℝ → ℝ := fun M q =>
    (((1 - q) ^ (M + 1))⁻¹ - ((1 + q) ^ (M + 1))⁻¹) / 2
  ∃ (qValue qDeriv : ℕ → ℝ),
    (∀ M : ℕ, 0 < M →
      0 < qValue M ∧
        qValue M < 1 ∧
        oddPacket M (qValue M) = 1 ∧
        ∀ q : ℝ, 0 < q → q < 1 →
          oddPacket M q = 1 → q = qValue M) ∧
      (∀ M : ℕ, 0 < M →
        0 < qDeriv M ∧
          qDeriv M < 1 ∧
          derivativeOddPacket M (qDeriv M) = 1 ∧
          (∀ q : ℝ, 0 < q → q < 1 →
            derivativeOddPacket M q = 1 → q = qDeriv M) ∧
          qDeriv M = qValue (M + 1)) ∧
      (∀ (M : ℕ) (q : ℝ), 0 < M → 0 < q → q < 1 →
        derivativeOddPacket M q < 1 → q < qDeriv M) ∧
      Filter.Tendsto
        (fun M : ℕ => (M : ℝ) * qValue M)
        Filter.atTop (nhds (Real.arsinh 1)) ∧
      Filter.Tendsto
        (fun M : ℕ => ((M : ℝ) + 1) * qDeriv M)
        Filter.atTop (nhds (Real.arsinh 1)) ∧
      Filter.Tendsto
        (fun M : ℕ =>
          -(1 / 2 : ℝ) * Real.log (qDeriv M) -
            ((1 / 2 : ℝ) * Real.log (M : ℝ) -
              (1 / 2 : ℝ) * Real.log (Real.arsinh 1)))
        Filter.atTop (nhds 0)

end MathlibPlus.Open.Analysis
