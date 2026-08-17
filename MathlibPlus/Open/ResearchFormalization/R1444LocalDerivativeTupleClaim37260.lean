import MathlibPlus.Open.ResearchFormalization.R1444QuinaryDerivative

namespace MathlibPlus.Open.ResearchFormalization.R1444LocalDerivativeTupleClaim37260

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1444

/-- Claim 37260: on the exact quinary chart carrier, the local derivative,
its ordered five conjugates, and their generated subgroup are the displayed
`δ_σ`, `(δ_σ^{ρ^k})`, and `B_σ`. -/
def claim37260 : Prop :=
  ∀ σ : quinaryPermutation,
    derivative5 σ = rho5⁻¹ * (σ⁻¹ * rho5 * σ) ∧
      (∀ k : Fin 5,
        derivativeTuple5 σ k =
          conjugateBy5 (rho5 ^ k.val) (derivative5 σ)) ∧
        derivativeClosure5 σ =
          Subgroup.closure (Set.range (derivativeTuple5 σ))

end

end MathlibPlus.Open.ResearchFormalization.R1444LocalDerivativeTupleClaim37260
