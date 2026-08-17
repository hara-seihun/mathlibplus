import MathlibPlus.Open.ResearchFormalization.R1181Suborbit

namespace MathlibPlus.Open.ResearchFormalization.R1181.Claim31924

open MathlibPlus.Open.ResearchFormalization.R1181Suborbit

/-- Claim 31924: the fixed section and the exact singleton/complement
point-stabilizer orbit split over the unique distinguished factor support. -/
def claim31924 {Ω : Type} {r : ℕ}
    (G M : Subgroup (Equiv.Perm Ω))
    (T : Fin r → Subgroup (Equiv.Perm Ω))
    (P : Set (Set Ω)) (C : Fin r → Set (Set Ω))
    (i₀ : Fin r) (B₀ : Set Ω) (α : Ω)
    (f : Set Ω → Ω) (F : Set Ω) : Prop :=
  disjointSupportSimpleSocleSetup G M T P C ∧
    uniqueFactorAt C i₀ B₀ ∧
      fixedSectionCondition (C i₀) B₀ α (T i₀) f F

end MathlibPlus.Open.ResearchFormalization.R1181.Claim31924
