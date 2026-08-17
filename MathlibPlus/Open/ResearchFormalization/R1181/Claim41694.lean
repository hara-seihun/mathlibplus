import MathlibPlus.Open.ResearchFormalization.R1181Suborbit

namespace MathlibPlus.Open.ResearchFormalization.R1181.Claim41694

open MathlibPlus.Open.ResearchFormalization.R1181Suborbit

variable {Ω : Type}

/-- Claim 41694: for a quotient block orbit contained in the distinguished
support, its fixed-section points and its complementary points are each one
transitive point-stabilizer orbit. -/
def claim41694 {r : ℕ}
    (G M : Subgroup (Equiv.Perm Ω))
    (T : Fin r → Subgroup (Equiv.Perm Ω))
    (P : Set (Set Ω)) (C : Fin r → Set (Set Ω))
    (i₀ : Fin r) (B₀ : Set Ω) (α : Ω)
    (f : Set Ω → Ω) (F : Set Ω)
    (O : Set (Set Ω)) : Prop :=
  (disjointSupportSimpleSocleSetup G M T P C ∧
    uniqueFactorAt C i₀ B₀ ∧
      fixedSectionCondition (C i₀) B₀ α (T i₀) f F ∧
        O ∈ quotientBlockOrbitFamily G P B₀ ∧
          O ⊆ C i₀) →
    fixedSectionOver f O ∈ pointStabilizerOrbits G α ∧
      complementarySectionOver f O ∈ pointStabilizerOrbits G α

end MathlibPlus.Open.ResearchFormalization.R1181.Claim41694
