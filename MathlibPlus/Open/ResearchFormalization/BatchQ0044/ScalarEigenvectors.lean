import MathlibPlus.Open.ResearchFormalization.ScalarBatch01

namespace MathlibPlus.Open.ResearchFormalization.BatchQ0044

/-- Claim 29305: the closed-only eigenvector family and its toric commutators. -/
def claim29305 : Prop :=
  (∀ d : ℕ, 2 ≤ d →
    qStar d =
      ∑ j ∈ Finset.Icc 1 (d - 1),
        (Nat.choose (d - 1) j : RootedRing) *
          xPoly 0 ^ (d - 1 - j) *
            (xPoly j - rootVariable ^ j * xPoly 0)) ∧
  (∀ d : ℕ, 2 ≤ d →
    rootedOperator (qStar d) = rootVariable * qStar d) ∧
  (∀ (a : RootedRing), a ∈ rootedFactorAlgebra →
    ∀ d : ℕ, 2 ≤ d →
      zFree (commutatorK a d) ∧
        (commutatorK a d).coeff 0 ∈ rankOneToricIdeal) ∧
  commutatorK scalarS 2 =
    Polynomial.C (xCoeff 0 * xCoeff 2 - xCoeff 1 ^ 2)

end MathlibPlus.Open.ResearchFormalization.BatchQ0044
