import Mathlib.NumberTheory.Chebyshev

/-!
# Chebyshev functions and FKS one-sided envelopes

Statement-fidelity registry nodes for admitted claims 766 and 769.
Decimal constants are exact rational values, and the displayed real exponent is
represented by `Real.rpow`.
-/

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-- Claim 766: the improved global one-sided theta envelope. -/
def improvedGlobalOneSidedThetaBound : Prop :=
  ∀ x : ℝ, 2 ≤ x →
    let L := Real.log x
    let R : ℝ := 55666305 / 10000000
    (Chebyshev.theta x - x) / x ≤
      (121096 / 1000 : ℝ) *
        Real.rpow (L / R) (3 / 2 : ℝ) *
        Real.exp (-2 * Real.sqrt (L / R))

/-- Claim 769: the global one-sided psi envelope at the improved amplitude. -/
def globalOneSidedPsiBound : Prop :=
  ∀ x : ℝ, 2 ≤ x →
    let L := Real.log x
    let R : ℝ := 55666305 / 10000000
    (Chebyshev.psi x - x) / x ≤
      (121096 / 1000 : ℝ) *
        Real.rpow (L / R) (3 / 2 : ℝ) *
        Real.exp (-2 * Real.sqrt (L / R))

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
