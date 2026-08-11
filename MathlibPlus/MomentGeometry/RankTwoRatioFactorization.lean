import Mathlib

/-!
# Rank-two moment-ratio factorization

The exact scalar factorization from packet `C-0011`, Record 3.  This complements the
separately queued ratio-scaling and feasibility statements.  The claim that the
left-hand scalar equals `1440` times the completed Bezout determinant is deliberately
not asserted here, because that linkage still requires a shared reviewed matrix
definition.
-/

namespace MathlibPlus.MomentGeometry

/-- Clearing the `R` and `S` denominators gives the packet's exact affine rank-two
factorization. -/
theorem rankTwoBezoutRatioFactorization
    (m₀ m₁ m₂ m₃ : ℝ) (hm₀ : m₀ ≠ 0) (hm₂ : m₂ ≠ 0) :
    m₀ * (3 * m₀ * m₁ * m₃ + 15 * m₁ ^ 2 * m₂ - 10 * m₀ * m₂ ^ 2) =
      m₀ ^ 2 * m₂ ^ 2 *
        (3 * (m₁ * m₃ / m₂ ^ 2) +
          15 * (m₁ ^ 2 / (m₀ * m₂)) - 10) := by
  field_simp [hm₀, hm₂]

end MathlibPlus.MomentGeometry
