import MathlibPlus.Open.Combinatorics.FixedSupportClaim26067

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R0516ComponentProfileDerivative26061

noncomputable section

/-- The literal marked-occurrence expansion of the order-`k` profile
 derivative.  Each connected component of order `k` contributes one copy of
 the residual component profile. -/
noncomputable def literalMarkedDerivative {V : Type*} [Fintype V]
    (T : SimpleGraph V) (k : ℕ) : MvPolynomial ℕ ℤ :=
  ∑ A : MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.EdgeState T,
    ∑ C : (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stateGraph A).ConnectedComponent,
      if MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.componentOrder (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stateGraph A) C = k then
        ((-1 : ℤ) ^ A.1.card) •
          MvPolynomial.monomial
            (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.componentProfile (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stateGraph A) - Finsupp.single k 1) 1
      else 0

/-- Claim 26061: differentiation in the order-`k` component-profile variable
is exactly the sum over literal marked component occurrences, retaining the
residual profile after one marked component is removed. -/
def claim26061 : Prop :=
  ∀ {V : Type*} [Fintype V]
    (T : SimpleGraph V) (k : ℕ),
    1 ≤ k →
      (∀ p : ℕ →₀ ℕ,
        MvPolynomial.pderiv k (MvPolynomial.monomial p (1 : ℤ)) =
          ((p k : ℕ) : ℤ) •
            MvPolynomial.monomial (p - Finsupp.single k 1) (1 : ℤ)) ∧
      (MvPolynomial.pderiv k (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stanleyComponentPolynomial T) =
          literalMarkedDerivative T k) ∧
      (∀ A : MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.EdgeState T,
        MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.componentProfile (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stateGraph A) k =
          ((Finset.univ.filter
              (fun C : (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stateGraph A).ConnectedComponent =>
                MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.componentOrder (MathlibPlus.Open.Combinatorics.FixedSupportClaim26067.stateGraph A) C = k)).card : ℕ))

end

end MathlibPlus.Open.ResearchFormalization.R0516ComponentProfileDerivative26061
