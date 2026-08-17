import MathlibPlus.Open.ResearchFormalization.R0761Claim24557

namespace MathlibPlus.Open.ResearchFormalization.R0761Claim24542

open MathlibPlus.Open.ResearchFormalization.R0761Claim24557

noncomputable section

/-- Claim 24542: inversion is trivial on an elementary-two kernel, so its
 generalized-dihedral carrier is elementary-two of one higher rank; the
 elementary-two CI boundary is exactly rank four, with rank five already
 giving the non-CI case. -/
def elementaryTwoGeneralizedDihedralCollapse_claim24542 : Prop :=
  (∀ d : ℕ, dihedralElementaryTwoIsomorphism d) ∧
    (∀ d : ℕ, undirectedCIGroup (d := d) ↔ d ≤ 4) ∧
      nonCIWitness (d := 5)

end

end MathlibPlus.Open.ResearchFormalization.R0761Claim24542
