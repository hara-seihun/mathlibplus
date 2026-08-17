import MathlibPlus.Open.ResearchFormalization.R1181Suborbit

namespace MathlibPlus.Open.ResearchFormalization.R1181Suborbit

noncomputable section

/-- Claim 31925: every quotient block-stabilizer action has a lift in the
point stabilizer, obtained through correction of a block-preserving lift with the
factor supported on the distinguished block-part. -/
def claim31925 : Prop :=
  ∀ {Ω : Type} [Fintype Ω] {r : ℕ}
    (G M : Subgroup (Equiv.Perm Ω))
    (T : Fin r → Subgroup (Equiv.Perm Ω))
    (P : Set (Set Ω)) (C : Fin r → Set (Set Ω))
    (i₀ : Fin r) (B₀ : Set Ω) (α : Ω)
    (f : Set Ω → Ω) (F : Set Ω),
    disjointSupportSimpleSocleSetup G M T P C →
    uniqueFactorAt C i₀ B₀ →
    fixedSectionCondition (Ω := Ω) (C i₀) B₀ α (T i₀) f F →
    (∀ g : G,
      (g : Equiv.Perm Ω) '' B₀ = B₀ →
      ∃ t : T i₀, ∃ h : Equiv.Perm Ω,
        h ∈ G ∧
        h = (t : Equiv.Perm Ω) * (g : Equiv.Perm Ω) ∧
        h α = α ∧
        (∀ B : Set Ω, B ∈ P →
          h '' B = (g : Equiv.Perm Ω) '' B)) ∧
    (∀ h : G, (h : Equiv.Perm Ω) α = α →
      (h : Equiv.Perm Ω) '' B₀ = B₀)

/-- Claim 41697 is the duplicate exact quotient-transporter implication,
using the reviewed finite simple-socle and point-suborbit carriers. -/
def claim41697 : Prop :=
  ∀ {Ω : Type} [Fintype Ω] {r : ℕ}
    (G M : Subgroup (Equiv.Perm Ω))
    (T : Fin r → Subgroup (Equiv.Perm Ω))
    (P : Set (Set Ω)) (C : Fin r → Set (Set Ω))
    (i₀ : Fin r) (B₀ : Set Ω) (α : Ω)
    (f : Set Ω → Ω) (F : Set Ω)
    (q : Equiv.Perm Ω),
    claim31930 (Ω := Ω) G M T P C i₀ B₀ α f F q

end
end MathlibPlus.Open.ResearchFormalization.R1181Suborbit
