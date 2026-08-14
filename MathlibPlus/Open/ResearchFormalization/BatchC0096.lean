import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Exact finite decomposition stated in Claim 1473, with the displayed exact
remainder and the amplitudes defined by the packet's rational values. -/
def claim_1473 : Prop :=
  ∃ N : ℕ, ∃ r : ℝ,
    0 < r ∧
    r < (1 : ℝ) / (10 : ℝ) ^ 100 ∧
    r = (9540953 : ℝ) /
      ((11346699 : ℝ) * (10 : ℝ) ^ 100) ∧
    (1 : ℝ) / 4.8568 - (1 : ℝ) / 4.8594 =
      (N : ℝ) * ((1 : ℝ) / (10 : ℝ) ^ 100) + r

end MathlibPlus.Open.ResearchFormalization
