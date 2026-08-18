import MathlibPlus.Open.ResearchFormalization.ScalarRootedFactors

namespace MathlibPlus.Open.ResearchFormalization.R0634Claim23505

open MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- Claim 23505: the displayed scalar rooted-factor algebra is not finitely
-generated as a `ℚ`-algebra. -/
def claim_23505 : Prop :=
  ¬ Algebra.FiniteType ℚ (scalarRootedFactorAlgebra : Type)

end

end MathlibPlus.Open.ResearchFormalization.R0634Claim23505
