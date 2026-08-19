import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0527RepeatedSpectrum

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

private noncomputable def homogeneousProductDifference
    {s : ℕ}
    (kappa : Fin s → Polynomial ℚ)
    (multiplicity : Fin s → ℕ)
    (jetSum : Fin s → Polynomial ℚ) : Polynomial (Polynomial ℚ) :=
  (∏ alpha : Fin s,
      (Polynomial.X + Polynomial.C (kappa alpha)) ^ (multiplicity alpha - 1)) *
    (∑ alpha : Fin s,
      Polynomial.C (jetSum alpha) *
        (Finset.univ.filter (fun beta : Fin s => beta ≠ alpha)).prod
          (fun beta => Polynomial.X + Polynomial.C (kappa beta)))

private def qConstantCoefficient
    (P : Polynomial (Polynomial ℚ)) : Prop :=
  ∀ n : ℕ, (P.coeff n).natDegree ≤ 0

/-- Claim 22401: with distinct nonconstant coarse values and their retained
multiplicities, a repeated coarse class makes the homogeneous normal-jet
trade vanish, and kills every classwise signed jet sum. -/
def claim22401 : Prop :=
  ∀ {s : ℕ}
    (a : Polynomial ℚ)
    (coarseMessage : Fin s → Polynomial ℚ)
    (multiplicity : Fin s → ℕ)
    (jetSum : Fin s → Polynomial ℚ),
    (∀ alpha : Fin s, 1 ≤ multiplicity alpha) →
      (∀ alpha : Fin s, 1 ≤ (coarseMessage alpha - a).natDegree) →
      (∀ alpha beta : Fin s, alpha ≠ beta →
        coarseMessage alpha - a ≠ coarseMessage beta - a) →
      (∃ alpha : Fin s, 2 ≤ multiplicity alpha) →
      qConstantCoefficient
        (homogeneousProductDifference
          (fun alpha => coarseMessage alpha - a)
          multiplicity jetSum) →
        homogeneousProductDifference
          (fun alpha => coarseMessage alpha - a)
          multiplicity jetSum = 0 ∧
          ∀ alpha : Fin s, jetSum alpha = 0

end

end MathlibPlus.Open.NewResearch2.R0527RepeatedSpectrum
