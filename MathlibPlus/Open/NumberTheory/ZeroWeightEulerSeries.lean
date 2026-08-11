import MathlibPlus.RepresentationTheory.ZeroWeightMultiplicity

/-!
# Zero-weight Euler series

This registry node records the local Hilbert-series identity and the global
Euler/Dirichlet-series identity from admitted claim 280. The coefficient at a
positive integer is written directly as the product over its exact prime
exponents, so no multiplicativity hypothesis is added.
-/

namespace MathlibPlus.Open.NumberTheory

/-- The zero-weight local Hilbert series and its multiplicative global
Dirichlet series. The shift `m + 1` indexes the positive integers. -/
def zeroWeightEulerSeries : Prop :=
  (PowerSeries.mk (R := ℚ)
      (fun k => ((k / 2 + 1 : ℕ) : ℚ)) =
    (1 - (PowerSeries.X : PowerSeries ℚ))⁻¹ *
      (1 - (PowerSeries.X : PowerSeries ℚ) ^ 2)⁻¹) ∧
  ∀ s : ℂ, 1 < s.re →
    HasSum
      (fun m : ℕ =>
        ((↑(∏ p ∈ (m + 1).primeFactors,
          ((m + 1).factorization p / 2 + 1)) : ℂ) *
          ((m + 1 : ℂ) ^ (-s))))
      (riemannZeta s * riemannZeta (2 * s))

end MathlibPlus.Open.NumberTheory
