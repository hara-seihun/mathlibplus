import MathlibPlus.Open.ResearchFormalization.R0530.Claim26098
import MathlibPlus.Open.ResearchFormalizationBatch019ffedf141b77c7b96e46e312eadae9

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0530Claim26110

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch
open MathlibPlus.Open.ResearchFormalization.BatchR0532
open MathlibPlus.Open.ResearchFormalization.R0530.Claim26098

noncomputable def leafCoefficient26110 (T : DoubleSpider) : ℚ :=
  (markedSingletonPolynomial (doubleSpiderGraph T)).coeff
    (Finsupp.single (doubleSpiderOrder T - 1) 1)

/-- Claim 26110: the coefficient of the order-minus-one pure component
    monomial in the marked singleton polynomial is exactly the total number
    of pendant legs. -/
def leafCountFromMarkedPolynomial_claim26110 : Prop :=
  ∀ T : DoubleSpider,
    admissibleDoubleSpider T →
      leafCoefficient26110 T =
        (T.left.card + T.right.card : ℚ)

end

end MathlibPlus.Open.ResearchFormalization.R0530Claim26110
