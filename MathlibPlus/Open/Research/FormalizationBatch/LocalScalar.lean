import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.FormalizationBatch

private noncomputable def pssSeries (p : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun r : ℕ =>
    Finset.sum (Finset.range (r + 1)) (fun j => ((p : ℚ)⁻¹) ^ j))

private def vacuumSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun r : ℕ => r + 1)

/-- The PSS scalar and harmonic vacuum have the supplied distinct local series. -/
def pssScalarDiffersFromHarmonicVacuum : Prop :=
  ∀ p : ℕ, Nat.Prime p →
    let p' : ℚ := p
    ((1 - PowerSeries.X : PowerSeries ℚ)⁻¹ *
        (1 - p'⁻¹ • PowerSeries.X)⁻¹ = pssSeries p) ∧
    ((1 - PowerSeries.X : PowerSeries ℚ)⁻¹ *
        (1 - PowerSeries.X : PowerSeries ℚ)⁻¹ = vacuumSeries) ∧
    PowerSeries.coeff 1 (pssSeries p) = 1 + p'⁻¹ ∧
    PowerSeries.coeff 1 vacuumSeries = 2 ∧
    2 - PowerSeries.coeff 1 (pssSeries p) = (p' - 1) / p' ∧
    0 < (p' - 1) / p' ∧
    PowerSeries.coeff 1 (pssSeries 2) = 3 / 2

end MathlibPlus.Open.Research.FormalizationBatch
