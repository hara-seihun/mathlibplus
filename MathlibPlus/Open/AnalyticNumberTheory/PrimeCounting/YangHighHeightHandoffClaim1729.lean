import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-- Claim 1729: the exact `L_*` identity and the high-height inclusion of
 the classical denominator-`4.83` region in Yang's logarithmic region. -/
def yangHighHeightHandoff_claim1729 : Prop :=
  let Lstar : ℝ := Real.exp ((19.62 : ℝ) / (4.83 : ℝ))
  (Real.log Lstar / (19.62 : ℝ) = 1 / (4.83 : ℝ)) ∧
    ∀ (t σ : ℝ),
      Real.exp Lstar ≤ t →
        (1 - 1 / ((4.83 : ℝ) * Real.log t) < σ →
          1 - Real.log (Real.log t) /
              ((19.62 : ℝ) * Real.log t) < σ)

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
