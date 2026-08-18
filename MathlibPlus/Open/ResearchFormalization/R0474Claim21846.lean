import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0474R0538

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0474Claim21846

open MathlibPlus.Open.ResearchFormalization.R0474R0538

/-- The length of the exact pulled-back support interval determined by the
endpoints `-1` and `1` of the reviewed partition profile. -/
noncomputable def cubicWindowWidth (j : ℕ) : ℝ :=
  (((j : ℝ) + 1) / 3) ^ 3 - (((j : ℝ) - 1) / 3) ^ 3

/-- Claim 21846: the reviewed flat Gevrey partition profile gives the
cubic-root windows and their exact pulled-back support width. -/
def claim21846_cubicRootFlatPartition : Prop :=
  ∀ χ : ℝ → ℝ, FlatGevreyPartitionProfile χ →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ j : ℕ, 1 ≤ j →
        (∀ t : ℝ, 0 ≤ t →
          cubicWindow χ j t ≠ 0 →
            (((j : ℝ) - 1) / 3) ^ 3 < t ∧
              t < (((j : ℝ) + 1) / 3) ^ 3) ∧
        c * Real.rpow (cubicCenter j) (2 / 3 : ℝ) ≤
            cubicWindowWidth j ∧
        cubicWindowWidth j ≤
          C * Real.rpow (cubicCenter j) (2 / 3 : ℝ)

end MathlibPlus.Open.ResearchFormalization.R0474Claim21846
