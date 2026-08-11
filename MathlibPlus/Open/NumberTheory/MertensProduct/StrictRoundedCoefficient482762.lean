import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.PrimeCounting

/-!
# Strict rounded Mertens-product bound

This registry node formalizes admitted claim 660. At a real cutoff `x`, the
product is over exactly the primes `p ≤ x`, represented using `Nat.floor x`.
-/

noncomputable section

namespace MathlibPlus.Open.NumberTheory.MertensProduct

/-- On the full half-line `x ≥ 286`, the prime product has the packet's strict
upper bound with the rounded coefficient `0.482762`. -/
def strictRoundedCoefficient482762 : Prop :=
  ∀ x : ℝ, 286 ≤ x →
    (∏ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime,
        (p : ℝ) / ((p : ℝ) - 1)) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        ((241381 : ℝ) / 500000) *
          Real.exp Real.eulerMascheroniConstant / Real.log x

end MathlibPlus.Open.NumberTheory.MertensProduct
