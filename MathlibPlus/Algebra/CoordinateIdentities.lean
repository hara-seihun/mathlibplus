import Mathlib

namespace MathlibPlus.Algebra.CoordinateIdentities

/-- Claim 45452: the two displayed Chern-coordinate inequalities and deficit
identity after the substitutions `c₁² = b` and `c₂ = 12a - b`.  The value
`c₁sq` denotes the Chern number `c₁²`; it is not assumed to be the square of a
separate square-root variable.  The source leaves the ambient ordered field
unstated, so exact rational coordinates are used here. -/
theorem chern_coordinate_translation
    (a b c₁sq c₂ : ℚ)
    (hc₁sq : c₁sq = b)
    (hc₂ : c₂ = 12 * a - b) :
    (5 * b ≥ c₂ - 36 ↔ b ≥ 2 * a - 6) ∧
      (b ≤ 3 * c₂ ↔ b ≤ 9 * a) ∧
      3 * c₂ - c₁sq = 4 * (9 * a - b) := by
  constructor
  · constructor <;> intro h <;> linarith [hc₂]
  constructor
  · constructor <;> intro h <;> linarith [hc₂]
  · rw [hc₁sq, hc₂]
    ring

/-- Claim 4165: after the displayed definitions of `D`, `d`, and `κ`, the
slope-rate identity is the stated algebraic identity.  The nonzero-denominator
hypothesis makes the displayed division an ordinary field identity. -/
theorem slope_rate_identity
    (β γ D d κ : ℝ)
    (hD : D = (β - 1) ^ 2 + γ ^ 2)
    (hD0 : D ≠ 0)
    (hd : d = D⁻¹)
    (hκ : κ = (β ^ 2 + γ ^ 2) / D - 1) :
    κ = (2 * β - 1) * d := by
  rw [hκ, hd]
  field_simp [hD0]
  rw [hD]
  ring
end MathlibPlus.Algebra.CoordinateIdentities
