import Mathlib

namespace MathlibPlus.Open.ResearchFormalization_01a000d9_2780_7396_aedf_f03df9d5e258

/--
Claim 11330: the sharp amplitude margin is the older square-modulus margin
minus the extra radial square; the implication follows, but the reverse
implication is not an algebraic consequence.
-/
def claim11330 : Prop :=
  ∀ (Aσ Aσσ κ₆ : ℝ),
    let 𝒜₆ := Aσ ^ 2 + Aσσ - κ₆
    let 𝒦₆ := 2 * Aσ ^ 2 + Aσσ - κ₆
    𝒦₆ = 𝒜₆ + Aσ ^ 2 ∧
      (𝒜₆ ≥ 0 → 𝒦₆ ≥ 0) ∧
      ∃ (x y k : ℝ),
        2 * x ^ 2 + y - k ≥ 0 ∧ ¬(x ^ 2 + y - k ≥ 0)

end MathlibPlus.Open.ResearchFormalization_01a000d9_2780_7396_aedf_f03df9d5e258
