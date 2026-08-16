import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeEulerCentralJetSingularity

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The canonical finite prime exhaustion `P_x = {p prime | p ≤ x}`. -/
def primeCutoff (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter Nat.Prime

/-- The central Euler weight of a prime. -/
noncomputable def primeCentralWeight (p : ℕ) : ℝ :=
  Real.rpow (p : ℝ) (-(1 : ℝ) / 2)

/-- The finite central Euler product `Q_{P_x}(0)`. -/
noncomputable def centralEulerProduct (x : ℕ) : ℝ :=
  ∏ p ∈ primeCutoff x, (1 - primeCentralWeight p)

/-- The finite holomorphic Euler multiplier from the translated numerator. -/
noncomputable def primeEulerMultiplier (x : ℕ) (z : ℂ) : ℂ :=
  ∏ p ∈ primeCutoff x,
    (1 - Complex.exp (((-(1 : ℂ) / 2) - z) *
      (Real.log (p : ℝ) : ℂ)))

/-- The first central coefficient of the logarithmic derivative of the
finite multiplier. -/
noncomputable def centralLogDerivative (x : ℕ) : ℂ :=
  deriv (primeEulerMultiplier x) 0 /
    primeEulerMultiplier x 0

/-- The real finite sum displayed for the central logarithmic derivative. -/
noncomputable def centralDerivativeSum (x : ℕ) : ℝ :=
  ∑ p ∈ primeCutoff x,
    primeCentralWeight p * Real.log (p : ℝ) /
      (1 - primeCentralWeight p)

/-- The central-normalized finite Euler germ. -/
noncomputable def centralNormalizedMultiplier (x : ℕ) (z : ℂ) : ℂ :=
  primeEulerMultiplier x z / primeEulerMultiplier x 0

/-- Its first Taylor coefficient at the central point. -/
noncomputable def centralNormalizedFirstCoefficient (x : ℕ) : ℂ :=
  deriv (centralNormalizedMultiplier x) 0

/-- The coefficientwise raw inverse and its central coefficient norm. -/
noncomputable def rawInverseCentralCoefficient (x : ℕ) : ℂ :=
  (primeEulerMultiplier x 0)⁻¹

noncomputable def rawInverseCentralCoefficientNorm (x : ℕ) : ℝ :=
  ‖rawInverseCentralCoefficient x‖

/-- Claim 15234: the prime-exhausted Euler inverse loses its central
coefficient, while the first coefficient of the central-normalized germ
also diverges, so neither germ has a finite coefficientwise limit. -/
def claim15234 : Prop :=
  (∀ x : ℕ,
      primeEulerMultiplier x 0 = (centralEulerProduct x : ℂ)) ∧
    Tendsto centralEulerProduct atTop (𝓝 0) ∧
    Tendsto rawInverseCentralCoefficientNorm atTop atTop ∧
    (∀ x : ℕ,
      centralLogDerivative x = (centralDerivativeSum x : ℂ)) ∧
    (∀ x : ℕ,
      centralNormalizedFirstCoefficient x = centralLogDerivative x) ∧
    Tendsto centralDerivativeSum atTop atTop ∧
    (¬ ∃ L : ℂ,
      Tendsto rawInverseCentralCoefficient atTop (𝓝 L)) ∧
    (¬ ∃ L : ℂ,
      Tendsto centralNormalizedFirstCoefficient atTop (𝓝 L))

end
end MathlibPlus.Open.AnalyticNumberTheory.PrimeEulerCentralJetSingularity
