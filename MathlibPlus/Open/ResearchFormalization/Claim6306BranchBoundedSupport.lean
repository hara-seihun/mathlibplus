import MathlibPlus.Open.ResearchFormalization.R3390BicentroidClaim50115
import MathlibPlus.Open.TraceBatch

namespace MathlibPlus.Open.ResearchFormalization.Claim6306BranchBoundedSupport

open MathlibPlus.Open.ResearchFormalization.R3390

noncomputable section

abbrev ComponentPolynomial := MvPolynomial ℕ ℚ
abbrev RootedFactorPolynomial := Polynomial ComponentPolynomial

/-- The genuine rooted factor on the component-part polynomial carrier, after
extending the integral U-polynomial coefficients to `ℚ`. -/
def genuineRootedFactorQ (R : R3390.RootedTree) : RootedFactorPolynomial :=
  (R3390.genuineRootedFactor R).map (MvPolynomial.map (Int.castRingHom ℚ))

def branchProduct (B : Multiset R3390.RootedTree) : RootedFactorPolynomial :=
  (B.map genuineRootedFactorQ).prod

def branchBound (B : Multiset R3390.RootedTree) : ℕ :=
  (B.map R3390.RootedTree.order).sup

/-- Claim 6306: every component part in every coefficient of the product of
 genuine rooted-tree factors is bounded by the largest branch order. -/
def branchBoundedCoefficientSupport_claim6306 : Prop :=
  ∀ (B : Multiset R3390.RootedTree),
    let P_B := branchProduct B
    let β := branchBound B
    ∀ (a : ℕ) (m : ℕ →₀ ℕ),
      m ∈ (P_B.coeff a).support →
        ∀ i ∈ m.support, i ≤ β

end
end MathlibPlus.Open.ResearchFormalization.Claim6306BranchBoundedSupport
