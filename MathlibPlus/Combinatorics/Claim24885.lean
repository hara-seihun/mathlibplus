import Mathlib

namespace MathlibPlus.Combinatorics.Claim24885

open scoped BigOperators

noncomputable section

/-- Claim 24885: the root-component-size marginal at `a` sums the profile
coefficients over exactly the rooted profiles containing `a`. -/
def rootComponentSizeMarginal_claim24885
    {R A β : Type*} [Fintype R] [AddCommMonoid β]
    (contains : R → A → Prop) [DecidableRel contains]
    (alpha : R → A → β) (a : A) : β :=
  ∑ rho ∈ Finset.univ.filter (fun rho => contains rho a), alpha rho a

end
end MathlibPlus.Combinatorics.Claim24885
