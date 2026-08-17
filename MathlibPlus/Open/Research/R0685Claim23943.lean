import Mathlib

namespace MathlibPlus.Open.Research.R0685

/-- The exact arithmetic survivor at `k = 46`. -/
def claim23943 : Prop :=
  ∀ u v : ℕ,
    u + v = 26 →
      2 * u + 3 * v ≤ 55 →
        3 ≤ v →
          v ≤ 3 ∧ u = 23 ∧ v = 3

end MathlibPlus.Open.Research.R0685
