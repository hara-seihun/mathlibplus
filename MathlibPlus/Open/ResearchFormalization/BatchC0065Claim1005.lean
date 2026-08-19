import MathlibPlus.Open.Analysis.SharpAllRankDegreeThreshold

namespace MathlibPlus.Open.ResearchFormalization.BatchC0065

open MathlibPlus.Open.Analysis

/-- Claim 1005: the explicit `q = 10⁷` seven-factor product has pairwise
 distinct positive reciprocal roots, simple strictly negative zeros, and a
negative signed rank-six determinant, hence a rank-six positivity failure. -/
def simpleStrictlyNegativeRootDegreeSevenCounterexample_claim1005 : Prop :=
  simpleRootQ = (10 : ℝ) ^ (7 : ℕ) ∧
    simpleRootReciprocals.Pairwise (· ≠ ·) ∧
    (∀ r ∈ simpleRootReciprocals, 0 < r) ∧
    simpleRootPolynomial.natDegree = 7 ∧
    simpleStrictlyNegativeRoots simpleRootPolynomial ∧
    karlinDet 6 simpleRootPolynomial 0 < 0 ∧
    (∃ x : ℝ, 0 ≤ x ∧ karlinDet 6 simpleRootPolynomial x < 0)

end MathlibPlus.Open.ResearchFormalization.BatchC0065
