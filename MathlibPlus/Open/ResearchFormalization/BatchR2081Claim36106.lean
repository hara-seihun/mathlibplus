import Mathlib
import MathlibPlus.Open.ResearchFormalization.InterpolationBatch

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization

/-- Exact transport of every old cardinal through one prefix insertion, together
with the resulting full Lebesgue-function formula. -/
def claim36106 : Prop :=
  ∀ (n : ℕ) (nodes : Fin n → ℝ) (y x : ℝ),
    Function.Injective nodes →
    (∀ i : Fin n, y ≠ nodes i) →
    (∀ i : Fin n, x ≠ nodes i) →
      (∀ i : Fin n,
        cardinal (appendNodes nodes y) (Fin.castSucc i) x =
          (nodeProduct nodes x / nodeProduct nodes y) *
            cardinal nodes i y *
              ((y - x) / (x - nodes i))) ∧
      lebesgue (appendNodes nodes y) x =
        |nodeProduct nodes x / nodeProduct nodes y| *
          (1 + |x - y| *
            ∑ i : Fin n, |cardinal nodes i y| / |x - nodes i|)

end MathlibPlus.Open.ResearchFormalization
