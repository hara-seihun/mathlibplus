import MathlibPlus.Open.ResearchFormalization.R1181Suborbit

namespace MathlibPlus.Open.ResearchFormalization.R1181Suborbit

variable {Ω : Type}

/-- The supported quotient-block orbit gives exactly the section and
nonsection point-stabilizer orbits. -/
def claim31927 {r : ℕ}
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

/-- Conjugation permutes the finite simple factors and their block supports;
point stabilizers preserve the distinguished factor, its point stabilizer, and
fixed section. -/
def factorPointStabilizerSet
    (T : Subgroup (Equiv.Perm Ω)) (α : Ω) : Set (Equiv.Perm Ω) :=
  {x | x ∈ T ∧ x α = α}

def claim41693 {r : ℕ}
    (G M : Subgroup (Equiv.Perm Ω))
    (T : Fin r → Subgroup (Equiv.Perm Ω))
    (P : Set (Set Ω)) (C : Fin r → Set (Set Ω))
    (i₀ : Fin r) (B₀ : Set Ω) (α : Ω)
    (f : Set Ω → Ω) (F : Set Ω) : Prop :=
  (disjointSupportSimpleSocleSetup G M T P C ∧
    uniqueFactorAt C i₀ B₀ ∧
      fixedSectionCondition (C i₀) B₀ α (T i₀) f F) →
    (∀ g : G, ∃ σ : Equiv.Perm (Fin r),
      ∀ i : Fin r,
        (∀ x : Equiv.Perm Ω,
          x ∈ T i ↔
            (g : Equiv.Perm Ω) * x * (g : Equiv.Perm Ω)⁻¹ ∈ T (σ i)) ∧
        (g : Equiv.Perm Ω) '' supportOf (T i) = supportOf (T (σ i)) ∧
        blockImage (g : Equiv.Perm Ω) (C i) = C (σ i)) ∧
    (∀ g : G, (g : Equiv.Perm Ω) α = α →
      (g : Equiv.Perm Ω) '' B₀ = B₀ ∧
        blockImage (g : Equiv.Perm Ω) (C i₀) = C i₀ ∧
          (∀ x : Equiv.Perm Ω,
            x ∈ T i₀ ↔
              (g : Equiv.Perm Ω) * x * (g : Equiv.Perm Ω)⁻¹ ∈ T i₀) ∧
            Set.image
                (fun x : Equiv.Perm Ω =>
                  (g : Equiv.Perm Ω) * x * (g : Equiv.Perm Ω)⁻¹)
                (factorPointStabilizerSet (T i₀) α) =
              factorPointStabilizerSet (T i₀) α ∧
              (g : Equiv.Perm Ω) '' F = F)

/-- The generated-conjugate point-suborbit criterion places the transporter in
 the two-closure. -/
def claim41698 : Prop :=
  ∀ (H : Subgroup (Equiv.Perm Ω)) (q : Equiv.Perm Ω) (α : Ω),
    MathlibPlus.Open.Research.OrbitalCriteria.transitiveSet
      (H : Set (Equiv.Perm Ω)) →
    q α = α →
    let G : Subgroup (Equiv.Perm Ω) :=
      Subgroup.closure
        ((H : Set (Equiv.Perm Ω)) ∪
          MathlibPlus.Open.Research.OrbitalCriteria.conjugateSet q
            (H : Set (Equiv.Perm Ω)))
    MathlibPlus.Open.Research.OrbitalCriteria.fixesStabilizerOrbits q
        (G : Set (Equiv.Perm Ω)) α →
      q ∈ MathlibPlus.Open.Research.OrbitalCriteria.twoClosureOf
        (G : Set (Equiv.Perm Ω))

end MathlibPlus.Open.ResearchFormalization.R1181Suborbit
