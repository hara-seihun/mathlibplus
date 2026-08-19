import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis.Claim4258

noncomputable def jensenGap4258 (t s : ℝ) : ℝ :=
  (Real.rpow t (2 / 3 : ℝ) + Real.rpow s (2 / 3 : ℝ)) / 2 -
    Real.rpow ((Real.sqrt t + Real.sqrt s) / 2) (4 / 3 : ℝ)

def exactJensenGap_claim4258 : Prop :=
  ∀ t s : ℝ, 0 < t → 0 < s →
    0 ≤ jensenGap4258 t s ∧
      (jensenGap4258 t s = 0 ↔ t = s)

end MathlibPlus.Open.Analysis.Claim4258

end
