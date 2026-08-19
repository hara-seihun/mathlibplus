import MathlibPlus.Open.ResearchFormalization.R0099EulerCurrent

namespace MathlibPlus.Open.ResearchFormalization.R0099EulerCurrentAfterDivision

open MathlibPlus.Open.ResearchFormalization.R0099EulerCurrent
open scoped BigOperators

noncomputable section

/-- Claim 17932: a bivariate quotient of the explicitly defined Euler current
has the stated anti-diagonal coefficient formula. -/
def coefficientFormulaAfterDivision_claim17932 : Prop :=
  ∀ (R : Type*) [CommRing R] (H : PowerSeries R)
    (C : BivariateSeries R),
    eulerDivisor * C = eulerCurrent H →
      ∀ i j : ℕ,
        PowerSeries.coeff j (PowerSeries.coeff i C) =
          ∑ a ∈ Finset.range (min i j + 1),
            ((antiDiagonalLength i j - 2 * a : ℕ) : R) *
              PowerSeries.coeff a H *
                PowerSeries.coeff (antiDiagonalLength i j - a) H

end

end MathlibPlus.Open.ResearchFormalization.R0099EulerCurrentAfterDivision
