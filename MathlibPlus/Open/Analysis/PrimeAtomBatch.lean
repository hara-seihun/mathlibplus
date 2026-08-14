import Mathlib

namespace MathlibPlus.Open.Analysis.PrimeAtom

noncomputable section

/-- The confluence-defined kernel contributed by one positive arithmetic atom. -/
def isolatedPrimeAtomKernel (a ell lambda mu : ℝ) : ℝ :=
  if lambda = mu then
    -(2 * a / lambda) * (1 + lambda * ell) * Real.exp (-lambda * ell)
  else
    4 * a * (lambda * Real.exp (-mu * ell) - mu * Real.exp (-lambda * ell)) /
      (mu ^ 2 - lambda ^ 2)

/-- The isolated positive atom has a strictly negative diagonal. -/
def isolatedPrimeAtomNegativeDiagonal : Prop :=
  ∀ (a ell lambda : ℝ),
    0 < a → 0 < ell → 0 < lambda →
      isolatedPrimeAtomKernel a ell lambda lambda =
          -(2 * a / lambda) * (1 + lambda * ell) * Real.exp (-lambda * ell) ∧
        isolatedPrimeAtomKernel a ell lambda lambda < 0

/-- The off-diagonal atom formula and its negative confluence diagonal. -/
def isolatedPrimeAtomKernelClaim : Prop :=
  ∀ (a ell lambda mu : ℝ),
    0 < a → 0 < ell → 0 < lambda → 0 < mu →
      ((lambda ≠ mu →
          isolatedPrimeAtomKernel a ell lambda mu =
            4 * a * (lambda * Real.exp (-mu * ell) - mu * Real.exp (-lambda * ell)) /
              (mu ^ 2 - lambda ^ 2)) ∧
        isolatedPrimeAtomKernel a ell lambda lambda =
          -(2 * a / lambda) * (1 + lambda * ell) * Real.exp (-lambda * ell) ∧
        isolatedPrimeAtomKernel a ell lambda lambda < 0)

end

end MathlibPlus.Open.Analysis.PrimeAtom
