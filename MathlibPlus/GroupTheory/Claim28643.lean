import MathlibPlus.Open.ResearchFormalization.R1067

namespace MathlibPlus.GroupTheory.R1075

open MathlibPlus.Open.ResearchFormalization.R1067

/-- Claim 28643: the displacement subgroup is the additive subgroup generated
by the normalized predecessor displacements on the concrete F3-square base. -/
def displacementSubgroup_claim28643
    (p : Equiv.Perm F3Square) : AddSubgroup F3Square :=
  displacementSubgroup p

end MathlibPlus.GroupTheory.R1075
