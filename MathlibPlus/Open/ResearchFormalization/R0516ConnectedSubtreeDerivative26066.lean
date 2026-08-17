import MathlibPlus.Open.Combinatorics.FixedSupportClaim26067

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R0516ConnectedSubtreeDerivative26066

noncomputable section

/-- Claim 26066: on a finite tree, the signed order-`k` profile derivative
is the once-counted sum of deleted-complement Stanley polynomials over
connected vertex supports of cardinality `k`. -/
def claim26066 : Prop :=
  ∀ {V : Type*} [Fintype V]
    (T : SimpleGraph V) (k : ℕ),
    T.IsTree →
      1 ≤ k →
        ((-1 : ℤ) ^ (k - 1)) •
            MvPolynomial.pderiv k
              (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stanleyComponentPolynomial T) =
          ∑ S : Finset V,
            if S.card = k ∧
                (T.induce (S : Set V)).Preconnected then
              MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.deletedStanleyPolynomial
                T S
            else 0

end

end MathlibPlus.Open.ResearchFormalization.R0516ConnectedSubtreeDerivative26066
