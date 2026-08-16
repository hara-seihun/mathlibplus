import MathlibPlus.Open.Analysis.ZetaHardyFormalization

namespace MathlibPlus.Open.Analysis.NymanCauchyIdentities15292_15293_15295

noncomputable section

open Set MeasureTheory
open MathlibPlus.Open.Analysis.ZetaHardy

/-- The critical Cauchy boundary energy used in claim 15292. -/
private def criticalCauchyEnergy15292 (c : ℕ → ℂ) : ℝ :=
  1 / (2 * Real.pi) *
    ∫ t : ℝ,
      ‖finitePoleCancelledFamily c
          ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 /
        (1 / 4 + t ^ 2)

/-- The discrete partial-sum energy in claim 15292. -/
private def discretePartialSumEnergy15292 (c : ℕ → ℂ) : ℝ :=
  ∑' n : ℕ,
    if 0 < n then
      ‖divisorPartialSum c (n : ℝ)‖ ^ 2 /
        ((n : ℝ) * ((n + 1 : ℕ) : ℝ))
    else 0

/-- The continuous partial-sum energy in claim 15292. -/
private def continuousPartialSumEnergy15292 (c : ℕ → ℂ) : ℝ :=
  ∫ y in Ici (1 : ℝ), ‖divisorPartialSum c y‖ ^ 2 / y ^ 2

/-- The two critical Cauchy norm identities from admitted claim 15292. -/
def criticalCauchyNormIdentities15292 : Prop :=
  ∀ c : ℕ → ℂ,
    finiteComplexCoefficients c →
    poleCancellationCondition c →
      criticalCauchyEnergy15292 c = discretePartialSumEnergy15292 c ∧
        criticalCauchyEnergy15292 c = continuousPartialSumEnergy15292 c

/-- The pointwise fractional-part map used in claim 15293. -/
private def literalNymanMap15293 (c : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' d : ℕ,
    if 0 < d then
      c d * ((Int.fract (1 / ((d : ℝ) * x)) : ℝ) : ℂ)
    else 0

/-- The literal pointwise reciprocal identity from admitted claim 15293. -/
def literalNymanPointwiseMap15293 : Prop :=
  ∀ c : ℕ → ℂ,
    finiteComplexCoefficients c →
    poleCancellationCondition c →
      ∀ y : ℝ, 1 < y →
        literalNymanMap15293 c (1 / y) = -divisorPartialSum c y

/-- The Dirichlet coefficient series at the center in claim 15295. -/
private def dirichletCenterSeries15295 (c : ℕ → ℂ) : ℂ :=
  ∑' n : ℕ,
    if 0 < n then
      divisorConvolutionCoefficient c n / (n : ℂ)
    else 0

/-- The center integral identity from admitted claim 15295, including the
Dirichlet coefficient series before the partial-sum series. -/
def centerIntegralIdentity15295 : Prop :=
  ∀ c : ℕ → ℂ,
    finiteComplexCoefficients c →
    poleCancellationCondition c →
      finitePoleCancelledFamily c 1 = dirichletCenterSeries15295 c ∧
        finitePoleCancelledFamily c 1 = centerPartialSumSeries c ∧
        finitePoleCancelledFamily c 1 = centerPartialSumIntegral c ∧
        nymanCenterIntegral c = -finitePoleCancelledFamily c 1

end

end MathlibPlus.Open.Analysis.NymanCauchyIdentities15292_15293_15295
