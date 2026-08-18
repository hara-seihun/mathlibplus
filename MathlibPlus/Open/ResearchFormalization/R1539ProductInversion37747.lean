import MathlibPlus.Open.ResearchFormalization.R1539GeneratedProductGroup37745

namespace MathlibPlus.Open.ResearchFormalization.R1539ProductInversion37747

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1539GeneratedProductGroup37745

abbrev A4 := alternatingGroup (Fin 4)
abbrev Omega := ZMod 5 × A4

def productInversion : Equiv.Perm Omega :=
  Equiv.prodCongr (Equiv.neg (ZMod 5)) (Equiv.inv A4)

def claim37747_productInversionConjugatesPair : Prop :=
  (∀ p : Equiv.Perm Omega,
    p ∈ H ↔ productInversion * p * productInversion⁻¹ ∈ K)

end

end MathlibPlus.Open.ResearchFormalization.R1539ProductInversion37747
