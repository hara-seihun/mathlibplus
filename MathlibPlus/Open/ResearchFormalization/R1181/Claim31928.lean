import MathlibPlus.Open.ResearchFormalization.R1181Suborbit

namespace MathlibPlus.Open.ResearchFormalization.R1181.Claim31928

open MathlibPlus.Open.ResearchFormalization.R1181Suborbit

/-- Claim 31928: every quotient block orbit disjoint from the distinguished
factor support is one point-stabilizer suborbit. -/
def claim31928 {Ω : Type} {r : ℕ}
    (G M : Subgroup (Equiv.Perm Ω))
    (T : Fin r → Subgroup (Equiv.Perm Ω))
    (P : Set (Set Ω)) (C : Fin r → Set (Set Ω))
    (i₀ : Fin r) (B₀ : Set Ω) (α : Ω)
    (O : Set (Set Ω)) : Prop :=
  (disjointSupportSimpleSocleSetup G M T P C ∧
    uniqueFactorAt C i₀ B₀ ∧
      α ∈ B₀ ∧
        O ∈ quotientBlockOrbitFamily G P B₀ ∧
          Disjoint O (C i₀)) →
    ∃ x, x ∈ unionOfBlocks O ∧
      pointStabilizerOrbit G α x = unionOfBlocks O

end MathlibPlus.Open.ResearchFormalization.R1181.Claim31928
