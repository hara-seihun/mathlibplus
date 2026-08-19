import Mathlib

namespace MathlibPlus.Analysis.CompletedCoefficientFormula

/-- Claim 13630: the formal-power-series coefficients of
`H(z)=b+(z-alpha)T(z)` have the displayed completed form. -/
def completedCoefficientFormula_claim13630 : Prop :=
  ∀ {R : Type*} [CommRing R] (b α : R) (t : ℕ → R),
    (PowerSeries.coeff 0
        (PowerSeries.C b +
          (PowerSeries.X - PowerSeries.C α) * PowerSeries.mk t) =
        b - α * t 0) ∧
      (∀ n : ℕ, 1 ≤ n →
        PowerSeries.coeff n
            (PowerSeries.C b +
              (PowerSeries.X - PowerSeries.C α) * PowerSeries.mk t) =
          t (n - 1) - α * t n)

end MathlibPlus.Analysis.CompletedCoefficientFormula
