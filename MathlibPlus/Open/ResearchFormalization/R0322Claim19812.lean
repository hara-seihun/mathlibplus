import MathlibPlus.Open.ResearchFormalization.R0322Claim19813

namespace MathlibPlus.Open.ResearchFormalization.R0322Claim19812

noncomputable section

abbrev CoefficientPolynomial := Polynomial ℚ

def partCountFactor (k : ℕ) (ell : Fin (k + 1)) : CoefficientPolynomial :=
  ((1 : CoefficientPolynomial) + Polynomial.X) ^ (ell : ℕ) *
    Polynomial.X ^ (k - (ell : ℕ))

/-- Claim 19812 on the fixed characteristic-zero coefficient carrier used by
 the generalized-degree specialization. -/
def partCountFactors_linearIndependent_claim19812 : Prop :=
  ∀ k : ℕ,
    LinearIndependent ℚ (fun ell : Fin (k + 1) => partCountFactor k ell)

end

end MathlibPlus.Open.ResearchFormalization.R0322Claim19812
