import MathlibPlus.Algebra.FiniteDifferenceNormalization

namespace MathlibPlus.Open.ResearchFormalization.R0530FixedSideRigidity26115

noncomputable section

open MathlibPlus.Algebra.Claim26113

/-- Positivity of every pendant-leg length. -/
def positiveLegs (C : Multiset ℕ) : Prop :=
  ∀ ell, ell ∈ C → 0 < ell

/-- Claim 26115: with the smaller fixed side and the larger-side leg count
fixed, equality of the exact connected-subtree polynomials recovers both the
trunk length and the larger side. -/
def claim26115 : Prop :=
  ∀ (A : Multiset ℕ) (α : ℕ)
    (B B' : Multiset ℕ) (c c' : ℕ),
    A.sum = α →
      positiveLegs A ∧
        positiveLegs B ∧
          positiveLegs B' ∧
            2 ≤ A.card ∧
              2 ≤ B.card ∧
                2 ≤ B'.card ∧
                  α < B.sum ∧
                    α < B'.sum ∧
                      B.card = B'.card ∧
                        1 ≤ c ∧
                          1 ≤ c' →
      MathlibPlus.Algebra.Claim26113.connectedSubtreePolynomial A B c =
          MathlibPlus.Algebra.Claim26113.connectedSubtreePolynomial A B' c' →
        c = c' ∧ B = B'

end

end MathlibPlus.Open.ResearchFormalization.R0530FixedSideRigidity26115
