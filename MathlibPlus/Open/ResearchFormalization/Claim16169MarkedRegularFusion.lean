import MathlibPlus.Open.GraphTheory.Claim16172CayleyFiber

namespace MathlibPlus.Open.ResearchFormalization.Claim16169MarkedRegularFusion

noncomputable section

open MathlibPlus.Open.GraphTheory

private def inverseClosed16169 {G : Type*} [Group G]
    (S : Set G) : Prop :=
  ∀ g, g ∈ S ↔ g⁻¹ ∈ S

/-- Two markings represent the same marked pair modulo simultaneous
    simultaneous precomposition with an automorphism of the abstract group. -/
def markingsModuloAut16169
    {G Ω : Type*} [Group G]
    {P Q : Subgroup (Equiv.Perm Ω)}
    (mP nP : G ≃* P) (mQ nQ : G ≃* Q) : Prop :=
  ∃ α : G ≃* G,
    nP = α.trans mP ∧ nQ = α.trans mQ

/-- The exact selected symmetric-fusion carrier, with both marked base-point
    connection sets retained as inverse-closed subsets of `G \ {1}`. -/
def markedRegularPairAndSelectedFusion_claim16169
    {G Ω : Type*} [Fintype G] [Group G] [Finite Ω]
    (P Q : Subgroup (Equiv.Perm Ω))
    (Γ : SimpleGraph Ω) (o : Ω)
    (mP : G ≃* P) (mQ : G ≃* Q) : Prop :=
  regularPermutationGroup16172 P ∧
    regularPermutationGroup16172 Q ∧
      selectedSymmetricFusion16172 Γ P Q ∧
        inverseClosed16169 (markedConnectionSet16172 Γ o mP) ∧
          inverseClosed16169 (markedConnectionSet16172 Γ o mQ)

end

end MathlibPlus.Open.ResearchFormalization.Claim16169MarkedRegularFusion
