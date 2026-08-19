import MathlibPlus.Open.ResearchFormalization.Claim6306BranchBoundedSupport
import MathlibPlus.Open.TraceBatch

namespace MathlibPlus.Open.ResearchFormalization.Claim6308

open MathlibPlus.Open.ResearchFormalization.Claim6306BranchBoundedSupport
open MathlibPlus.Open.ResearchFormalization.R3390
open MathlibPlus.Open.TraceBatch

noncomputable def assembledNodePolynomial
    (B : Multiset R3390.RootedTree) :
    Claim6306BranchBoundedSupport.ComponentPolynomial :=
  rootClosure (Polynomial.X * branchProduct B)

noncomputable def pureRowContribution
    (j : ℕ)
    (P : Claim6306BranchBoundedSupport.RootedFactorPolynomial) :
    Claim6306BranchBoundedSupport.ComponentPolynomial :=
  MvPolynomial.X j * P.coeff (j - 1)

/-- A nonzero residual with a monic weighted context is exposed in the first
pure row above the branch-order bound. -/
def monicContextResidualSeparation : Prop :=
  ∀ (B B' : Multiset R3390.RootedTree)
    (C A Bprime : Claim6306BranchBoundedSupport.RootedFactorPolynomial)
    (c β : ℕ),
    monicWeightedTraceContext C c →
    (∀ R : R3390.RootedTree, R ∈ B → R3390.RootedTree.order R ≤ β) →
    (∀ R : R3390.RootedTree, R ∈ B' → R3390.RootedTree.order R ≤ β) →
    branchProduct B - branchProduct B' = C * (A - Bprime) →
    A - Bprime ≠ 0 →
    let q : ℕ := (A - Bprime).natDegree
    c + q + 1 > β →
      assembledNodePolynomial B ≠ assembledNodePolynomial B' ∧
        pureRowContribution (c + q + 1)
          (branchProduct B - branchProduct B') ≠ 0

end MathlibPlus.Open.ResearchFormalization.Claim6308
