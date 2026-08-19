import MathlibPlus.Open.ResearchFormalization.R0666Claim29476

namespace MathlibPlus.Open.ResearchFormalization.R0666Claim29475

open MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- Claim 29475: in the exact rooted-factor carrier, the scalar coordinate
`s = x₁ + z` subalgebra and the span of the triangular fiber coordinates
`e₂,e₃,…` form the stated direct-sum decomposition of `A_F`. -/
def claim29475 : Prop :=
  vectorSpaceDirectSum
    scalarSubalgebra.toSubmodule
    (conductorIdeal.restrictScalars ℚ)
    scalarRootedFactorAlgebra.toSubmodule

end

end MathlibPlus.Open.ResearchFormalization.R0666Claim29475
