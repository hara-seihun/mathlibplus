import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2777Claim35779

noncomputable section
open scoped BigOperators

private def dyadicWeight (j : ℕ) : ℝ :=
  (j : ℝ) / (2 : ℝ) ^ j

private def positivePeriodSupport : Set ℕ :=
  {j | ∃ k : ℕ, j = 6 * k + 3 ∨ j = 6 * k + 4}

private def negativePeriodSupport : Set ℕ :=
  {j | ∃ k : ℕ, j = 6 * k + 1 ∨ j = 6 * k + 6}

private noncomputable def finiteSupportWeightSum
    (S : Set ℕ) (K : ℕ) : ℝ := by
  classical
  exact ∑ j ∈ (Finset.range (6 * K + 1)).filter (fun j => j ∈ S),
    dyadicWeight j

/-- Claim 35779: the exact discrepancy after `K` complete period-six blocks. -/
def claim_35779_finitePeriodDiscrepancy : Prop :=
  ∀ K : ℕ,
    finiteSupportWeightSum positivePeriodSupport K -
        finiteSupportWeightSum negativePeriodSupport K =
      (2 * K : ℝ) / (64 : ℝ) ^ K

end

end MathlibPlus.Open.ResearchFormalization.R2777Claim35779
