import Mathlib

namespace MathlibPlus.Analysis.CompletedGeneratingSeries

noncomputable section

/-- Exact completed-series coefficient carrier and both coefficient identities
for `A(z)=1/2+(z-1/4)T(z)`. -/
def coefficientIdentities : Prop :=
  ∀ (T : PowerSeries ℝ),
    let A : PowerSeries ℝ :=
      PowerSeries.C (1 / 2 : ℝ) +
        (PowerSeries.X - PowerSeries.C (1 / 4 : ℝ)) * T
    PowerSeries.coeff 0 A =
        (1 / 2 : ℝ) - (1 / 4 : ℝ) * PowerSeries.coeff 0 T ∧
      ∀ n : ℕ, 1 ≤ n →
        PowerSeries.coeff n A =
          PowerSeries.coeff (n - 1) T -
            (1 / 4 : ℝ) * PowerSeries.coeff n T

end

end MathlibPlus.Analysis.CompletedGeneratingSeries
