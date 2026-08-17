import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2777Claim35777

noncomputable section
open scoped BigOperators

private def dyadicWeight (j : ℕ) : ℝ :=
  (j : ℝ) / (2 : ℝ) ^ j

private def positivePeriodSupport : Set ℕ :=
  {j | ∃ k : ℕ, j = 6 * k + 3 ∨ j = 6 * k + 4}

private def negativePeriodSupport : Set ℕ :=
  {j | ∃ k : ℕ, j = 6 * k + 1 ∨ j = 6 * k + 6}

private noncomputable def supportWeightSum (S : Set ℕ) : ℝ := by
  classical
  exact ∑' j : ℕ, if j ∈ S then dyadicWeight j else 0

/-- Claim 35777: the two disjoint infinite periodic supports are distinct
binary representations of `32/49` under the exact weight `j/2^j`. -/
def claim_35777_periodicDoubleRepresentation : Prop :=
  Set.Infinite positivePeriodSupport ∧
    Set.Infinite negativePeriodSupport ∧
      Disjoint positivePeriodSupport negativePeriodSupport ∧
        positivePeriodSupport ≠ negativePeriodSupport ∧
          supportWeightSum positivePeriodSupport = 32 / 49 ∧
            supportWeightSum negativePeriodSupport = 32 / 49

end

end MathlibPlus.Open.ResearchFormalization.R2777Claim35777
