import MathlibPlus.Open.Research.R1599A7Goursat

namespace MathlibPlus.Open.ResearchFormalization.Batch_7e3f7a79_Claim39494

open MathlibPlus.Open.Research.R1599A7Goursat

abbrev Point7 := Fin 7
abbrev S7 := Equiv.Perm Point7
abbrev A7 := alternatingGroup Point7

/-- The displayed regular seven-cycle, its local derivative, and its
synchronous conjugate tuple are the exact R-1599 objects. -/
def claim39494 : Prop :=
  ∀ σ : S7,
    let ρ : S7 := rho7
    let δ : S7 := ρ⁻¹ * conjugate7 ρ σ
    let 𝒟 : Fin 7 → S7 := fun i => conjugate7 δ (ρ ^ i.val)
    (∀ i : Fin 7, 𝒟 i = derivativeTuple7 σ i) ∧
      (a7Type7 σ ↔
        Subgroup.closure (Set.range 𝒟) = A7)

end MathlibPlus.Open.ResearchFormalization.Batch_7e3f7a79_Claim39494
