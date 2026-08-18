import MathlibPlus.Open.ResearchFormalization.R0530Claim26120

namespace MathlibPlus.Open.ResearchFormalization.R0530Claim26103

open MathlibPlus.Open.ResearchFormalization.BatchR0532
open MathlibPlus.Open.ResearchFormalization.R0530Claim26120

noncomputable section

/-- The smaller side total of a double spider. -/
def smallerSideTotal (T : DoubleSpider) : ℕ :=
  min T.left.sum T.right.sum

/-- Whether the two pendant-side totals agree. -/
def sideTotalsEqual (T : DoubleSpider) : Prop :=
  T.left.sum = T.right.sum

/-- The number of legs on the larger-total side when the totals differ. -/
def largerSideCount (T : DoubleSpider) : ℕ :=
  if T.left.sum < T.right.sum then T.right.card else T.left.card

/-- The global multiplicity of one leg length. -/
def globalLegMultiplicity (T : DoubleSpider) (a : ℕ) : ℕ :=
  (globalLegMultiset T).count a

/-- The degree sequence together with the canonically oriented first boundary jet. -/
def degreeAndBoundaryJet (T : DoubleSpider) :
    BivariatePoly × Polynomial ℤ :=
  (degreePolynomial T, (boundaryAndMarkedSurface T).1)

/-- Claim 26103: equality of the degree sequence and first connected-subtree
boundary jet determines the complete first recovery data, with the larger-side
count compared as an exchange-invariant quantity. -/
def claim26103 : Prop :=
  ∀ T T' : DoubleSpider,
    admissibleDoubleSpider T →
      admissibleDoubleSpider T' →
        degreeAndBoundaryJet T = degreeAndBoundaryJet T' →
          smallerSideTotal T = smallerSideTotal T' ∧
            (sideTotalsEqual T ↔ sideTotalsEqual T') ∧
            (∀ a : ℕ, a < smallerSideTotal T →
              globalLegMultiplicity T a = globalLegMultiplicity T' a) ∧
            (¬ sideTotalsEqual T →
              largerSideCount T = largerSideCount T') ∧
            globalLegMultiplicity T (smallerSideTotal T) =
              globalLegMultiplicity T' (smallerSideTotal T)

end

end MathlibPlus.Open.ResearchFormalization.R0530Claim26103
