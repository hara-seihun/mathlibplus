import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0177Claim12387

/-- Claim 12387: the exact stronger de Bruijn--Newman bound implies the
recorded weaker bound, with the displayed reserve. -/
def claim12387 : Prop :=
  (7 / 40 : ℝ) = 0.175 ∧
    (7 / 40 : ℝ) < 37272481 / 200000000 ∧
    (37272481 / 200000000 : ℝ) = 0.186362405 ∧
    (37272481 / 200000000 : ℝ) - 7 / 40 =
      2272481 / 200000000 ∧
    (2272481 / 200000000 : ℝ) = 0.011362405 ∧
    ∀ Λ : ℝ, Λ ≤ 7 / 40 → Λ ≤ 37272481 / 200000000

end MathlibPlus.Open.ResearchFormalization.O0177Claim12387
