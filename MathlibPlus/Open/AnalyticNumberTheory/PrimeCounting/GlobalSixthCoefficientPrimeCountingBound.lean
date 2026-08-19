import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

noncomputable section

/-- Claim 725: the C-0046 sixth-coefficient majorant bounds real prime
counting on the complete domain `x > 1`, with the real cutoff interpreted by
`Nat.floor`. -/
def globalSixthCoefficientPrimeCountingBound : Prop :=
  let F₆ : ℝ → ℝ := fun x =>
    let L := Real.log x
    x / L + x / L ^ 2 + 2 * x / L ^ 3 +
      6.024334 * x / L ^ 4 +
      24.024334 * x / L ^ 5 +
      120 * x / L ^ 6 +
      720 * x / L ^ 7 +
      6097.2 * x / L ^ 8
  ∀ x : ℝ, 1 < x →
    (Nat.primeCounting (Nat.floor x) : ℝ) < F₆ x

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
