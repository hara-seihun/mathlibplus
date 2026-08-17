import MathlibPlus.Open.ResearchFormalization.FormalizationBatch01a006da

namespace MathlibPlus.Open.ResearchFormalization.Claim10595

open MathlibPlus.Open.ResearchFormalization

/-- Claim 10595: for the exact positive two-atom moment carrier, the zeroth
and positive-index moments and both integer-normalized completed-Bezout
quantities have the displayed formulas. -/
def claim10595_exactTwoAtomCompletedBezoutFormulas : Prop :=
  ∀ A B z : ℝ, 0 < A → 0 < B → 0 < z →
    twoAtomMoment A B z 0 = A + B ∧
      (∀ j : ℕ, 1 ≤ j → twoAtomMoment A B z j = B * z ^ j) ∧
      twoAtomRankTwoQuantity A B z = twoAtomRankTwoFormula A B z ∧
      twoAtomRankThreeQuantity A B z = twoAtomRankThreeFormula A B z

end MathlibPlus.Open.ResearchFormalization.Claim10595
