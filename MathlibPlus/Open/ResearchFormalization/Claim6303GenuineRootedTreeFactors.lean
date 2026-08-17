import MathlibPlus.Open.ResearchFormalization.Claim6306BranchBoundedSupport

namespace MathlibPlus.Open.ResearchFormalization.Claim6303GenuineRootedTreeFactors

open MathlibPlus.Open.ResearchFormalization.R3390
open MathlibPlus.Open.ResearchFormalization.Claim6306BranchBoundedSupport

noncomputable section

/-- The weight of a component-part monomial, with `x_i` carrying weight `i`. -/
def componentMonomialWeight (m : ℕ →₀ ℕ) : ℕ :=
  m.sum (fun i a => i * a)

/-- Homogeneity in `z` and the component variables: `z` has weight one and
`x_i` has weight `i`. -/
def weightedHomogeneous
    (P : RootedFactorPolynomial) (n : ℕ) : Prop :=
  ∀ a ∈ P.support, ∀ m ∈ (P.coeff a).support,
    a + componentMonomialWeight m = n

/-- Claim 6303: for every rooted tree, the mapped genuine rooted factor has
weight equal to the tree order, is monic in `z`, and has that exact `z`-degree. -/
def genuineRootedTreeFactors_claim6303 : Prop :=
  ∀ R : R3390.RootedTree,
    let F_R := genuineRootedFactorQ R
    weightedHomogeneous F_R (R3390.RootedTree.order R) ∧
      F_R.Monic ∧ F_R.natDegree = R3390.RootedTree.order R

end
end MathlibPlus.Open.ResearchFormalization.Claim6303GenuineRootedTreeFactors
