import MathlibPlus.Open.ResearchFormalizationBatchClaims4780_4818_59849

namespace MathlibPlus.Open.ResearchFormalizationD0057

open MathlibPlus.Open.ResearchFormalizationBatch

/-- Claim 4817, with the reviewed exact rational isolations replacing the
source's decimal prefixes. -/
def positiveRootCountRankFourWallPolynomial_claim4817 : Prop :=
  ∃ x y : ℝ,
    0 < x ∧ x < y ∧ y < 4 * Real.pi ∧
    Polynomial.eval x rankFourWallPolynomial = 0 ∧
    Polynomial.eval y rankFourWallPolynomial = 0 ∧
    (16782052469 : ℝ) / 10000000000 < x ∧
      x < (16782052470 : ℝ) / 10000000000 ∧
    (536113359988346505777 : ℝ) / 100000000000000000000 < y ∧
      y < (536113359988346505778 : ℝ) / 100000000000000000000 ∧
    (∀ z : ℝ,
      0 < z → Polynomial.eval z rankFourWallPolynomial = 0 → z = x ∨ z = y)

end MathlibPlus.Open.ResearchFormalizationD0057
