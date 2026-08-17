import MathlibPlus.Open.ResearchFormalization.ScalarRootedFactors

namespace MathlibPlus.Open.ResearchFormalization

/-- Claim 23504: the scalar algebra is non-Noetherian, with its conductor
kernel as a non-finitely generated ideal. -/
def claim_23504 : Prop :=
  ¬ IsNoetherianRing ScalarRing ∧
    ¬ scalarRingKernelIdeal.FG

/-- Claim 23506: the scalar algebra is integrally closed while remaining
non-Noetherian. -/
def claim_23506 : Prop :=
  IsIntegrallyClosed ScalarRing ∧
    ¬ IsNoetherianRing ScalarRing

end MathlibPlus.Open.ResearchFormalization
