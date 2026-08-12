import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Independence.Integration

open MeasureTheory
open ProbabilityTheory
open scoped ProbabilityTheory

namespace MathlibPlus.Probability

/-- Claim 9279: covariance vanishes for distinct independent prime observables.

The prime labels are retained explicitly in the interface; the proof uses only
independence and integrability, as the source claim asserts. -/
theorem claim9279_covariance_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ)
    (hXY : X ⟂ᵢ[μ] Y) : ProbabilityTheory.covariance X Y μ = 0 := by
  let mX : ℝ := ∫ ω, X ω ∂μ
  let mY : ℝ := ∫ ω, Y ω ∂μ
  have hprod : Integrable (X * Y) μ := hXY.integrable_mul hX hY
  have hprod_eq : (∫ ω, X ω * Y ω ∂μ) = mX * mY := by
    dsimp [mX, mY]
    exact hXY.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable
  have hsub1 :
      (∫ ω, X ω * Y ω - mY * X ω ∂μ) =
        (∫ ω, X ω * Y ω ∂μ) - (∫ ω, mY * X ω ∂μ) := by
    rw [integral_sub]
    · exact hprod
    · exact hX.const_mul mY
  have hsub2 :
      (∫ ω, (X ω * Y ω - mY * X ω) - mX * Y ω ∂μ) =
        (∫ ω, X ω * Y ω - mY * X ω ∂μ) - (∫ ω, mX * Y ω ∂μ) := by
    rw [integral_sub]
    · exact hprod.sub (hX.const_mul mY)
    · exact hY.const_mul mX
  have hadd :
      (∫ ω, ((X ω * Y ω - mY * X ω) - mX * Y ω) + mX * mY ∂μ) =
        (∫ ω, (X ω * Y ω - mY * X ω) - mX * Y ω ∂μ) +
          (∫ _ω, mX * mY ∂μ) := by
    rw [integral_add]
    · exact (hprod.sub (hX.const_mul mY)).sub (hY.const_mul mX)
    · exact integrable_const _
  change (∫ ω, (X ω - mX) * (Y ω - mY) ∂μ) = 0
  calc
    (∫ ω, (X ω - mX) * (Y ω - mY) ∂μ) =
        ∫ ω, ((X ω * Y ω - mY * X ω) - mX * Y ω) + mX * mY ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with ω
          ring
    _ = ((∫ ω, X ω * Y ω ∂μ) - (∫ ω, mY * X ω ∂μ)) -
          (∫ ω, mX * Y ω ∂μ) + (∫ _ω, mX * mY ∂μ) := by
          rw [hadd, hsub2, hsub1]
    _ = 0 := by
      rw [hprod_eq]
      simp_rw [integral_const_mul, integral_const, probReal_univ, one_smul]
      ring

end MathlibPlus.Probability
