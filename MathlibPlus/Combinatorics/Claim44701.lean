import Mathlib

namespace MathlibPlus.Combinatorics

/-- The sharp-trace linear relation forces the stated fibre-count lower bound
when the all-one fibre is absent and the normalized zero fibre is at least 9.
The names of the counts follow the source packet. -/
theorem sharpTraceCountLowerBound_claim44701
    (a y₀ y₁ y₂ z : ℤ)
    (hrel : a = y₀ + y₁ + y₂ + 2 * z - 17)
    (hz : z = 0)
    (ha : 9 ≤ a) :
    26 ≤ y₀ + y₁ + y₂ := by
  omega

end MathlibPlus.Combinatorics
