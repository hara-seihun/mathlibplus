import Mathlib

/-!
# Certified prime-counting and Chebyshev-theta endpoint data

Statement-fidelity registry node for admitted claim 639.
-/

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-- At `x₀ = 10^18`, the exact prime count and the stated lower bound for
Chebyshev's theta function hold. Replacing `θ(x₀)` by that lower endpoint in the
partial-summation majorant `J` gives a pointwise upper majorant `J⁺`. -/
noncomputable def endpointThetaAndPrimeCountMajorant : Prop :=
  let x₀ : ℝ := 10 ^ 18
  let η : ℝ := 0.024334
  let θLower : ℝ := 999999999144115634
  let J : ℝ → ℝ := fun x =>
    (Nat.primeCounting (10 ^ 18) : ℝ) - Chebyshev.theta x₀ / Real.log x₀ +
      x / Real.log x + η * x / Real.log x ^ 4 +
      ∫ t in x₀..x, (1 / Real.log t ^ 2 + η / Real.log t ^ 5)
  let Jplus : ℝ → ℝ := fun x =>
    (Nat.primeCounting (10 ^ 18) : ℝ) - θLower / Real.log x₀ +
      x / Real.log x + η * x / Real.log x ^ 4 +
      ∫ t in x₀..x, (1 / Real.log t ^ 2 + η / Real.log t ^ 5)
  Nat.primeCounting (10 ^ 18) = 24739954287740860 ∧
    θLower ≤ Chebyshev.theta x₀ ∧
    ∀ x : ℝ, J x ≤ Jplus x

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
