import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0387Claim20768

/-- Claim 20768: the literal positive-witness and sharpened contraction
inequalities force every private-coordinate deficit to be at least seven. -/
def privateCoordinateDeficit_ge_seven_claim20768 : Prop :=
  ∀ (D_w D_y : ℕ),
    1 ≤ D_w →
    2 * D_w ≤ D_y - 5 →
    7 ≤ D_y

end MathlibPlus.Open.ResearchFormalization.R0387Claim20768
