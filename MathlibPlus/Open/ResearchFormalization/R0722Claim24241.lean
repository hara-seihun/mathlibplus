import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0722Claim24241

open scoped InnerProductSpace

/-- The normalized vector attached to a pair of unit vectors. -/
noncomputable def normalizedPairVector {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : E :=
  (Real.sqrt (2 + 2 * ⟪x, y⟫_ℝ))⁻¹ • (x + y)

/-- Claim 24241: for an edge or nonedge pair, the displayed normalized sum
is a unit vector whenever its denominator is nonzero. -/
def normalizedPairUnit_claim24241 : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E),
    ‖x‖ = 1 →
      ‖y‖ = 1 →
        2 + 2 * ⟪x, y⟫_ℝ ≠ 0 →
          ‖normalizedPairVector x y‖ = 1

end MathlibPlus.Open.ResearchFormalization.R0722Claim24241
