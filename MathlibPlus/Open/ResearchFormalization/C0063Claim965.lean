import MathlibPlus.Open.ResearchFormalization.Batch.Polynomial

namespace MathlibPlus.Open.Analysis.Karlin

noncomputable section

open MathlibPlus.Open.ResearchFormalization.Batch.Polynomial

/-- Claim 965, using the admitted polynomial carrier `R` and its reviewed
monomial-symmetric orbit convention. -/
def explicitFourteenOrbitFormula_claim965 : Prop :=
  MathlibPlus.Open.ResearchFormalization.Batch.Polynomial.R =
    10800 * monomialSymmetric p7
      - 4200 * monomialSymmetric p52
      + 4200 * monomialSymmetric p511
      - 5600 * monomialSymmetric p43
      + 5040 * monomialSymmetric p421
      - 3360 * monomialSymmetric p4111
      + 5110 * monomialSymmetric p331
      + 7896 * monomialSymmetric p322
      - 5208 * monomialSymmetric p3211
      + 13146 * monomialSymmetric p31111
      - 7560 * monomialSymmetric p2221
      + 16352 * monomialSymmetric p22111
      - 56840 * monomialSymmetric p211111
      + 524895 * monomialSymmetric p1111111

end

end MathlibPlus.Open.Analysis.Karlin
