import MathlibPlus.Open.Analysis.BatchChannelPolynomials

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- The finite order-`r` channel polynomial is the finite sum of its
Poisson--Charlier basis terms. -/
def finiteChannelPolynomial_claim4459 : Prop :=
  ∀ (S : Finset ℕ) (S_f : ℕ → ℝ) (r : ℕ),
    finiteChannelPolynomial S S_f r =
      ∑ n ∈ S, Polynomial.C (S_f n) * finiteChannelBasis n r

end MathlibPlus.Open.Analysis
