import Mathlib

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch
def claim6959_shiftedGammaCarrierAndPositiveKernel : Prop := by
  exact ∀ (μ σ : ℝ),
    let a := μ + σ / 2
    let Cμ : ℂ → ℂ := fun s =>
      Complex.cpow (Real.pi : ℂ) (-s / 2) * Complex.Gamma (μ + s / 2)
    let gμσ : ℝ → ℝ := fun u =>
      2 * Real.rpow Real.pi μ * Real.exp ((2 * μ + σ) * u - Real.pi * Real.exp (2 * u))
    a > 0 → (∀ u, 0 < gμσ u) ∧ Integrable gμσ volume ∧
      (∀ s, Cμ s =
        Complex.cpow (Real.pi : ℂ) (-s / 2) * Complex.Gamma (μ + s / 2))

end MathlibPlus.Open.ResearchFormalizationLargeBatch
