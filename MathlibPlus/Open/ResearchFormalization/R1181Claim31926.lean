import MathlibPlus.Open.ResearchFormalization.R1181Suborbit

namespace MathlibPlus.Open.ResearchFormalization.R1181Claim31926

open MathlibPlus.Open.ResearchFormalization.R1181Suborbit

noncomputable section

/-- Conjugation of a concrete permutation set. -/
def conjugateSet31926 {Ω : Type*}
    (g : Equiv.Perm Ω) (H : Set (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) :=
  {x | ∃ h ∈ H, x = g * h * g⁻¹}

/-- The point stabilizer subset of a factor. -/
def factorPointStabilizer31926 {Ω : Type*}
    (T : Subgroup (Equiv.Perm Ω)) (α : Ω) : Set (Equiv.Perm Ω) :=
  {x | ∃ t : T, x = (t : Equiv.Perm Ω) ∧ x α = α}

/-- Claim 31926: under the exact disjoint-support simple-socle and fixed
section setup, factors/support parts are permuted; point-stabilizer elements
fix the distinguished block and its unique support part, normalize the factor
and its point stabilizer, and preserve the fixed section. -/
def claim31926 {r : ℕ} {Ω : Type}
    (G M : Subgroup (Equiv.Perm Ω))
    (T : Fin r → Subgroup (Equiv.Perm Ω))
    (P : Set (Set Ω)) (C : Fin r → Set (Set Ω))
    (i₀ : Fin r) (B₀ : Set Ω) (α : Ω)
    (f : Set Ω → Ω) (F : Set Ω) : Prop :=
  (disjointSupportSimpleSocleSetup G M T P C ∧
      uniqueFactorAt C i₀ B₀ ∧
        fixedSectionCondition (C i₀) B₀ α (T i₀) f F) →
    (∀ g : G, ∀ i : Fin r,
      ∃ j : Fin r,
        conjugateSet31926 (g : Equiv.Perm Ω) (T i) = (T j : Set _) ∧
          (g : Equiv.Perm Ω) '' (supportOf (Ω := Ω) (T i)) =
              (supportOf (Ω := Ω) (T j)) ∧
          (g : Equiv.Perm Ω) '' (⋃₀ (C i)) = ⋃₀ (C j)) ∧
      (∀ g : G, (g : Equiv.Perm Ω) α = α →
        (g : Equiv.Perm Ω) '' B₀ = B₀ ∧
          (g : Equiv.Perm Ω) '' (⋃₀ (C i₀)) = ⋃₀ (C i₀) ∧
          conjugateSet31926 (g : Equiv.Perm Ω) (T i₀ : Set _) =
              (T i₀ : Set _) ∧
          conjugateSet31926 (g : Equiv.Perm Ω)
              (factorPointStabilizer31926 (T i₀) α) =
            factorPointStabilizer31926 (T i₀) α ∧
          (g : Equiv.Perm Ω) '' F = F)

end

end MathlibPlus.Open.ResearchFormalization.R1181Claim31926
