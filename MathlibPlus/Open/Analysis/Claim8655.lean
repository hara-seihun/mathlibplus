import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Faithful registry node for the stated consecutive central-node gap.  The
indexing function and the no-eigenvalue-between condition keep the source's
meaning of "consecutive" explicit. -/
def consecutiveCentralNodeGap_claim8655 : Prop :=
  ∀ (N i : ℕ) (rho aStar aPrev Lambda TV : ℝ)
    (eigenvalue : ℕ → ℝ),
    0 < N →
    eigenvalue i < eigenvalue (i + 1) →
    (∀ j : ℕ,
      ¬ (eigenvalue i < eigenvalue j ∧
        eigenvalue j < eigenvalue (i + 1))) →
    |eigenvalue i| ≤ 2 * rho * aStar →
    |eigenvalue (i + 1)| ≤ 2 * rho * aStar →
    eigenvalue (i + 1) - eigenvalue i ≥
      Real.pi * aPrev * (1 - rho) / ((N : ℝ) * (1 + rho)) *
        Real.exp (-Lambda * TV)

end MathlibPlus.Open.Analysis
