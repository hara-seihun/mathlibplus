import MathlibPlus.Algebra.FiniteDifferenceNormalization
import MathlibPlus.Open.ResearchFormalization.Claim26123

namespace MathlibPlus.Open.ResearchFormalization.R0530Claim26125

open MathlibPlus.Algebra.Claim26113
open MathlibPlus.Open.ResearchFormalization.Claim26123
open Polynomial

noncomputable section

/-- The exact carrier of two positive, equal-sum, two-leg multisets. -/
def equalSumTwoLegMultisets (A A' : Multiset ℕ) : Prop :=
  positiveLegMultiset A ∧
    positiveLegMultiset A' ∧
      A.card = 2 ∧ A'.card = 2 ∧ A.sum = A'.sum

/-- Claim 26125: the unit-transfer difference has the exact normalized
subtree factorization, and equality of the corresponding subtree polynomials
recovers the two-leg multiset. -/
def claim26125 : Prop :=
  ∀ A A' : Multiset ℕ,
    equalSumTwoLegMultisets A A' →
      ∀ c : ℕ, 1 ≤ c →
        normalizedSubtreePolynomial A (A' + ({1} : Multiset ℕ)) c -
              normalizedSubtreePolynomial A' (A + ({1} : Multiset ℕ)) c =
            Polynomial.X * (1 - Polynomial.X ^ c) *
              (jPolynomial A' - jPolynomial A) ∧
          (connectedSubtreePolynomial A (A' + ({1} : Multiset ℕ)) c =
              connectedSubtreePolynomial A' (A + ({1} : Multiset ℕ)) c →
            jPolynomial A = jPolynomial A' ∧
              pathProduct A = pathProduct A' ∧ A = A')

end

end MathlibPlus.Open.ResearchFormalization.R0530Claim26125
