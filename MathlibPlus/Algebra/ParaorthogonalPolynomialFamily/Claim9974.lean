import MathlibPlus.Open.ResearchFormalizationBatch9978

namespace MathlibPlus.Algebra.ParaorthogonalPolynomialFamily

open MathlibPlus.Open.ResearchFormalizationBatch9978

noncomputable section

/-- Claim 9974: the displayed finite paraorthogonal family consists of
reciprocal polynomials of the stated degree. -/
def reciprocalParaorthogonalFamily : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    (paraorthogonalP m).reverse = paraorthogonalP m ∧
      (paraorthogonalP m).natDegree = paraorthogonalD m ∧
      ∀ τ : ℝ,
        (paraorthogonalQ m τ).reverse = paraorthogonalQ m τ ∧
          (paraorthogonalQ m τ).natDegree = paraorthogonalD m

end

end MathlibPlus.Algebra.ParaorthogonalPolynomialFamily
