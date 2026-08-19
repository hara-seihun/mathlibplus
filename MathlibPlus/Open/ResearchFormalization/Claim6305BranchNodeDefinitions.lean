import MathlibPlus.Open.ResearchFormalization.Claim6306BranchBoundedSupport
import MathlibPlus.Open.TraceBatch

namespace MathlibPlus.Open.ResearchFormalization.Claim6305

noncomputable section

open MathlibPlus.Open.ResearchFormalization.Claim6306BranchBoundedSupport
open MathlibPlus.Open.TraceBatch
open MathlibPlus.Open.ResearchFormalization.R3390

abbrev BranchMultiset := Multiset R3390.RootedTree
abbrev BranchProductPolynomial :=
  MathlibPlus.Open.ResearchFormalization.Claim6306BranchBoundedSupport.RootedFactorPolynomial
abbrev NodePolynomial :=
  MathlibPlus.Open.ResearchFormalization.Claim6306BranchBoundedSupport.ComponentPolynomial

/-- The assembled rooted node polynomial `U_Node(B)=Φ(z P_B)` on the exact
rooted-tree factor and root-closure carriers. -/
def assembledNodePolynomial6305 (B : BranchMultiset) : NodePolynomial :=
  rootClosure (Polynomial.X * branchProduct B)

end

end MathlibPlus.Open.ResearchFormalization.Claim6305
