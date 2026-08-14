import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The finite positive-multiplicity shell total-growth law. -/
def finitePositiveMultiplicityShellTotalGrowthLaw
    {I : Type*} [Fintype I] (re im : I → ℝ) (m : I → ℤ) : Prop :=
  let Ω : ℝ → I → ℤ := fun T i =>
    if (1 / 2 : ℝ) < re i ∧ |im i| < T then m i else 0
  (∀ S T : ℝ, S ≤ T →
      (∑ i, Ω T i) - ∑ i, Ω S i =
        ∑ i : I, if (1 / 2 : ℝ) < re i ∧ S ≤ |im i| ∧ |im i| < T then m i else 0) ∧
    ((∀ i, 0 < m i) →
      ∀ S T : ℝ, S ≤ T →
        ((∑ i, Ω S i) < ∑ i, Ω T i ↔
          ∃ i, (1 / 2 : ℝ) < re i ∧ S ≤ |im i| ∧ |im i| < T))

end MathlibPlus.Open.Analysis
