import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.BTYBatch

/-- Claim 1469: the endpoint function has the certified negative derivative. -/
def claim_1469 : Prop :=
  let Astar : ℝ := 1 / 4.8568
  let Aseed : ℝ := 1 / 4.8594
  let H : ℝ := 3 * 10 ^ 12
  let Lstar : ℝ := Real.exp (19.62 * Astar)
  let endpointFunction : ℝ → ℝ → ℝ := fun seed L =>
    let q : ℝ := seed / (seed + (10 : ℝ) ^ (-100 : ℤ))
    let c : ℝ := Real.log (16 + 1 / 300)
    let C₁ : ℝ → ℝ := fun μ =>
      0.87637 + 0.12002 * μ + 0.01017 * μ ^ 2 - 0.00073 * μ ^ 3
    let C₂ : ℝ → ℝ := fun η => 13.47 * η - 167 * η ^ 2 - 8300 * η ^ 3
    C₁ (q * L / (L + c)) + C₂ (seed / L) - 10 ^ (-7 : ℤ)
  ∀ L : ℝ,
    Real.log H ≤ L ∧ L ≤ Lstar →
      let F : ℝ → ℝ := endpointFunction Aseed
      HasDerivAt F (deriv F L) L ∧ deriv F L < -0.0002409

end MathlibPlus.Open.Research.BTYBatch
