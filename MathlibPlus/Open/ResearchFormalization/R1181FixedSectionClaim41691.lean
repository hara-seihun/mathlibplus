import MathlibPlus.Open.ResearchFormalization.R1181Suborbit

namespace MathlibPlus.Open.ResearchFormalization.R1181FixedSectionClaim41691

open MathlibPlus.Open.ResearchFormalization.R1181Suborbit

/-- Claim 41691: on the finite displayed simple-socle/block carrier, the
factor containing the distinguished block has the exact two point-stabilizer
orbits on each supported block, and their singleton points form the fixed
section. -/
def fixedSectionTwoOrbitCondition_claim41691 {Ω : Type} {r : ℕ}
    (G M : Subgroup (Equiv.Perm Ω))
    (T : Fin r → Subgroup (Equiv.Perm Ω))
    (P : Set (Set Ω)) (C : Fin r → Set (Set Ω))
    (i₀ : Fin r) (B₀ : Set Ω) (α : Ω)
    (f : Set Ω → Ω) (F : Set Ω) : Prop :=
  disjointSupportSimpleSocleSetup G M T P C ∧
    uniqueFactorAt C i₀ B₀ ∧
      fixedSectionCondition (C i₀) B₀ α (T i₀) f F

end MathlibPlus.Open.ResearchFormalization.R1181FixedSectionClaim41691
