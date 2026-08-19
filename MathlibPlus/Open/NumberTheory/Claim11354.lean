import Mathlib

namespace MathlibPlus.NumberTheory.Claim11354

open scoped BigOperators

/-- Claim 11354: the four prime-index coefficients of the standard
finite coefficient-preserving truncation of
`q * prod_{n >= 1} (1 - q^n)^24` through degree seven. -/
def ramanujanCoefficientsThroughSeven_claim11354 : Prop :=
  let Δ : PowerSeries ℤ :=
    PowerSeries.X *
      ∏ m ∈ Finset.Icc 1 7, (1 - PowerSeries.X ^ m) ^ 24
  PowerSeries.coeff 2 Δ = -24 ∧
    PowerSeries.coeff 3 Δ = 252 ∧
    PowerSeries.coeff 5 Δ = 4830 ∧
    PowerSeries.coeff 7 Δ = -16744

end MathlibPlus.NumberTheory.Claim11354
