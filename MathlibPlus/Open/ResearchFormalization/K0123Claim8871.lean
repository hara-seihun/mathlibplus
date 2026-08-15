import MathlibPlus.Open.ResearchFormalization.K0123

namespace MathlibPlus.Open.ResearchFormalization.K0123

/-- The exact `log 6` crossing in the saturated region, including its displayed decimal approximations and uniqueness. -/
def claim8871 : Prop :=
  ∃ zStar : ℝ,
    b < zStar ∧
      holeAction zStar = Real.log 6 ∧
      (3.130749088556830760 : ℝ) ≤ zStar ∧
      zStar < (3.130749088556830761 : ℝ) ∧
      (0.319412374391512197 : ℝ) ≤ zStar⁻¹ ∧
      zStar⁻¹ < (0.319412374391512198 : ℝ) ∧
      StrictMonoOn holeAction (Set.Ioi b) ∧
      ∀ z : ℝ, b < z → holeAction z = Real.log 6 → z = zStar

end MathlibPlus.Open.ResearchFormalization.K0123
