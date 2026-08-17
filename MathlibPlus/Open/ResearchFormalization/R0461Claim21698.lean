import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0461Claim21698

noncomputable section

/-- Claim 21698: the elementary correction components, with the exact
    phase-normalization formulas supplied by Claim 21697, obey all displayed
    zeroth through third derivative bounds on `x ≥ 1`. -/
def elementaryCorrectionDerivativeBounds_claim21698 : Prop :=
  let theta : ℝ → ℝ := fun x => Real.arctan (1 / x)
  let h : ℝ → ℝ := fun x => Real.log (1 + x⁻¹ ^ 2)
  let aOne : ℝ → ℝ := fun x => h x / 4 - 1 / (1 + x ^ 2)
  let bOne : ℝ → ℝ := fun x => -theta x / 2 - 3 * x / (1 + x ^ 2)
  ∀ x : ℝ, 1 ≤ x →
    0 ≤ theta x ∧
      theta x ≤ 1 / x ∧
      0 ≤ h x ∧
      h x ≤ 1 / x ^ 2 ∧
      |aOne x| ≤ 5 / (4 * x ^ 2) ∧
      |deriv aOne x| ≤ 3 / (2 * x ^ 3) ∧
      |deriv (deriv aOne) x| ≤ 5 / x ^ 4 ∧
      |deriv (deriv (deriv aOne)) x| ≤ 56 / x ^ 5 ∧
      |bOne x| ≤ 7 / (2 * x) ∧
      |deriv bOne x| ≤ 7 / (2 * x ^ 2) ∧
      |deriv (deriv bOne) x| ≤ 24 / x ^ 3 ∧
      |deriv (deriv (deriv bOne)) x| ≤ 144 / x ^ 4

end

end MathlibPlus.Open.ResearchFormalization.R0461Claim21698
