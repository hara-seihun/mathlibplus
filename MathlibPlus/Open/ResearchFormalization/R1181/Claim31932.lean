import MathlibPlus.Open.ResearchFormalization.R1181Suborbit

namespace MathlibPlus.Open.ResearchFormalization.R1181.Claim31932

open MathlibPlus.Open.ResearchFormalization.R1181Suborbit
open MathlibPlus.Open.Research.OrbitalCriteria

variable {Ω : Type}

/-- Claim 31932: in the aligned prime-fibre simple-socle carrier, a
transporter that preserves the distinguished factor support and fixed
section only needs the quotient block-suborbit check.  The complete
point-stabilizer suborbit transport and the two-closure conclusion then
follow, without a whole-cover normalization premise. -/
def claim31932 : Prop :=
  ∀ {r : ℕ}
    (G M : Subgroup (Equiv.Perm Ω))
    (T : Fin r → Subgroup (Equiv.Perm Ω))
    (P : Set (Set Ω)) (C : Fin r → Set (Set Ω))
    (i₀ : Fin r) (B₀ : Set Ω) (α : Ω)
    (f : Set Ω → Ω) (F : Set Ω)
    (H : Subgroup (Equiv.Perm Ω)) (q : Equiv.Perm Ω),
    (disjointSupportSimpleSocleSetup G M T P C ∧
      uniqueFactorAt C i₀ B₀ ∧
        fixedSectionCondition (C i₀) B₀ α (T i₀) f F ∧
          transitiveSet (H : Set (Equiv.Perm Ω)) ∧
            q α = α ∧
              G = Subgroup.closure
                ((H : Set (Equiv.Perm Ω)) ∪
                  conjugateSet q (H : Set (Equiv.Perm Ω))) ∧
                blockImage q P = P ∧
                  blockImage q (C i₀) = C i₀ ∧
                    q '' F = F ∧
                      (∀ O, O ∈ quotientBlockOrbitFamily G P B₀ →
                        blockImage q O = O)) →
      (∀ S, S ∈ pointStabilizerOrbits G α → q '' S = S) ∧
        q ∈ twoClosureOf (G : Set (Equiv.Perm Ω))

end MathlibPlus.Open.ResearchFormalization.R1181.Claim31932
