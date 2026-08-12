import Mathlib

namespace MathlibPlus.AlgebraicGeometry

/-- Claim 14613: the literal integer Noether-inequality check from the
packet.  The packet's displayed values are `c₁² = 5` and `c₂ = 7`; this
formalization records that arithmetic check and does not assert the geometric
existence of the underlying surface. -/
theorem noetherInequalityCheck14613 :
    let c₁sq : ℤ := 5
    let c₂ : ℤ := 7
    5 * c₁sq = 25 ∧
      (25 : ℤ) ≥ c₂ - 36 ∧
      c₂ - 36 = (-29 : ℤ) := by
  norm_num

end MathlibPlus.AlgebraicGeometry
