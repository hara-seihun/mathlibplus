import Mathlib

namespace MathlibPlus.Open.Research.R1162

abbrev C3Pow7 := Multiplicative (Fin 7 → ZMod 3)

def RegularPermutationSubgroup {Ω : Type} [DecidableEq Ω]
    (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ a b : Ω, ∃! r : R, (r : Equiv.Perm Ω) a = b

def TransitivePermutationSubgroup {Ω : Type} [DecidableEq Ω]
    (X : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ a b : Ω, ∃ g : X, (g : Equiv.Perm Ω) a = b

def BlockFor {Ω : Type} [DecidableEq Ω]
    (X : Subgroup (Equiv.Perm Ω)) (B : Set Ω) : Prop :=
  B.Nonempty ∧
    ∀ g : X, (g : Equiv.Perm Ω) '' B = B ∨
      Disjoint ((g : Equiv.Perm Ω) '' B) B

def PrimitivePermutationSubgroup {Ω : Type} [DecidableEq Ω]
    (X : Subgroup (Equiv.Perm Ω)) : Prop :=
  TransitivePermutationSubgroup X ∧
    ∀ B : Set Ω, BlockFor X B → Set.Subsingleton B ∨ B = Set.univ

def TwoClosureMember {Ω : Type} [DecidableEq Ω]
    (X : Subgroup (Equiv.Perm Ω)) (g : Equiv.Perm Ω) : Prop :=
  ∀ a b : Ω, ∃ x : X,
    (x : Equiv.Perm Ω) a = g a ∧ (x : Equiv.Perm Ω) b = g b

def ConjugateInsideTwoClosure {Ω : Type} [DecidableEq Ω]
    (R T X : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ g : Equiv.Perm Ω,
    TwoClosureMember X g ∧
      (∀ r : R, g * (r : Equiv.Perm Ω) * g⁻¹ ∈ T) ∧
      (∀ t : T, g⁻¹ * (t : Equiv.Perm Ω) * g ∈ R)

def claim31710 : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω]
    (R T : Subgroup (Equiv.Perm Ω)),
    Fintype.card Ω = 2187 →
      Nonempty (R ≃* C3Pow7) →
        Nonempty (T ≃* C3Pow7) →
          RegularPermutationSubgroup R →
            RegularPermutationSubgroup T →
              let X : Subgroup (Equiv.Perm Ω) := R ⊔ T
              PrimitivePermutationSubgroup X →
                ConjugateInsideTwoClosure R T X

def claim41474 : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω]
    (R T : Subgroup (Equiv.Perm Ω)),
    Fintype.card Ω = 2187 →
      Nonempty (R ≃* C3Pow7) →
        Nonempty (T ≃* C3Pow7) →
          RegularPermutationSubgroup R →
            RegularPermutationSubgroup T →
              let X : Subgroup (Equiv.Perm Ω) := R ⊔ T
              PrimitivePermutationSubgroup X →
                ConjugateInsideTwoClosure R T X

end MathlibPlus.Open.Research.R1162

namespace MathlibPlus.Open.Research.R1162

def SimpleUndirectedCayleyGraph (adj : C3Pow7 → C3Pow7 → Prop) : Prop :=
  (∀ x, ¬ adj x x) ∧
    (∀ x y, adj x y ↔ adj y x) ∧
      (∀ a x y, adj (a * x) (a * y) ↔ adj x y)

def GraphAutomorphism (adj : C3Pow7 → C3Pow7 → Prop)
    (g : Equiv.Perm C3Pow7) : Prop :=
  ∀ x y, adj (g x) (g y) ↔ adj x y

def ConjugateByGraphAutomorphism (adj : C3Pow7 → C3Pow7 → Prop)
    (R T : Subgroup (Equiv.Perm C3Pow7)) : Prop :=
  ∃ g : Equiv.Perm C3Pow7,
    GraphAutomorphism adj g ∧
      (∀ r : R, g * (r : Equiv.Perm C3Pow7) * g⁻¹ ∈ T) ∧
      (∀ t : T, g⁻¹ * (t : Equiv.Perm C3Pow7) * g ∈ R)

def claim31718 : Prop :=
  ∀ (adj : C3Pow7 → C3Pow7 → Prop),
    SimpleUndirectedCayleyGraph adj →
      ∀ (R T : Subgroup (Equiv.Perm C3Pow7)),
        Nonempty (R ≃* C3Pow7) →
          Nonempty (T ≃* C3Pow7) →
            RegularPermutationSubgroup R →
              RegularPermutationSubgroup T →
                (∀ r : R, GraphAutomorphism adj (r : Equiv.Perm C3Pow7)) →
                  (∀ t : T, GraphAutomorphism adj (t : Equiv.Perm C3Pow7)) →
                    let X : Subgroup (Equiv.Perm C3Pow7) := R ⊔ T
                    PrimitivePermutationSubgroup X →
                      ConjugateByGraphAutomorphism adj R T

end MathlibPlus.Open.Research.R1162

namespace MathlibPlus.Open.Research.R1162

def claim41482 : Prop :=
  ∀ (adj : C3Pow7 → C3Pow7 → Prop),
    SimpleUndirectedCayleyGraph adj →
      ∀ (R T : Subgroup (Equiv.Perm C3Pow7)),
        Nonempty (R ≃* C3Pow7) →
          Nonempty (T ≃* C3Pow7) →
            RegularPermutationSubgroup R →
              RegularPermutationSubgroup T →
                (∀ r : R, GraphAutomorphism adj (r : Equiv.Perm C3Pow7)) →
                  (∀ t : T, GraphAutomorphism adj (t : Equiv.Perm C3Pow7)) →
                    let X : Subgroup (Equiv.Perm C3Pow7) := R ⊔ T
                    PrimitivePermutationSubgroup X →
                      ConjugateByGraphAutomorphism adj R T

end MathlibPlus.Open.Research.R1162

namespace MathlibPlus.Open.Research.R1162

abbrev ProductIndex := Fin 3
abbrev BaseNine := ZMod 3 × ZMod 3
abbrev ProductActionPoints := ProductIndex → BaseNine
abbrev C3SquaredCubed := Multiplicative (ProductIndex → BaseNine)

def CoordinatePermutation (π : Equiv.Perm ProductIndex) :
    Equiv.Perm ProductActionPoints :=
  Equiv.piCongrLeft' (fun _ : ProductIndex => BaseNine) π

def PointwisePermutation (a : ProductIndex → Equiv.Perm BaseNine) :
    Equiv.Perm ProductActionPoints :=
  Equiv.piCongrRight a

def WreathElement (a : ProductIndex → Equiv.Perm BaseNine)
    (π : Equiv.Perm ProductIndex) : Equiv.Perm ProductActionPoints :=
  (CoordinatePermutation π).trans (PointwisePermutation a)

def ProductActionGroup : Subgroup (Equiv.Perm ProductActionPoints) :=
  Subgroup.closure {
    g | ∃ (a : ProductIndex → Equiv.Perm BaseNine)
          (π : Equiv.Perm ProductIndex),
        (∀ i, a i ∈ alternatingGroup BaseNine) ∧
          g = WreathElement a π }

def Translation (t : ProductActionPoints) : Equiv.Perm ProductActionPoints :=
  WreathElement (fun i => Equiv.addRight (t i)) 1

def TranslationSubgroup : Subgroup (Equiv.Perm ProductActionPoints) :=
  Subgroup.closure (Set.range Translation)

def HammingDistance (v w : ProductActionPoints) : ℕ :=
  (Finset.univ.filter (fun i => v i ≠ w i)).card

def TwoTransitivePermutationSubgroup {Ω : Type} [DecidableEq Ω]
    (X : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ a b c d : Ω, a ≠ b → c ≠ d →
    ∃ g : X, (g : Equiv.Perm Ω) a = c ∧ (g : Equiv.Perm Ω) b = d

def HammingDistanceOrbital (d : ℕ) : Prop :=
  ∀ v w v' w' : ProductActionPoints,
    HammingDistance v w = d → HammingDistance v' w' = d →
      ∃ g : ProductActionGroup,
        (g : Equiv.Perm ProductActionPoints) v = v' ∧
          (g : Equiv.Perm ProductActionPoints) w = w'

def DistinctHammingOrbitals : Prop :=
  HammingDistanceOrbital 1 ∧ HammingDistanceOrbital 2 ∧
    ∃ v₁ w₁ v₂ w₂ : ProductActionPoints,
      HammingDistance v₁ w₁ = 1 ∧
        HammingDistance v₂ w₂ = 2 ∧
          ¬ ∃ g : ProductActionGroup,
            (g : Equiv.Perm ProductActionPoints) v₁ = v₂ ∧
              (g : Equiv.Perm ProductActionPoints) w₁ = w₂

def claim31720 : Prop :=
  Fintype.card ProductActionPoints = 729 ∧
    (∀ b : BaseNine, Equiv.addRight b ∈ alternatingGroup BaseNine) ∧
      TranslationSubgroup ≤ ProductActionGroup ∧
        Nonempty (TranslationSubgroup ≃* C3SquaredCubed) ∧
          RegularPermutationSubgroup TranslationSubgroup ∧
            (∀ t : ProductActionPoints, t ≠ 0 →
              ∀ v : ProductActionPoints,
                (Translation t : Equiv.Perm ProductActionPoints) v ≠ v) ∧
              PrimitivePermutationSubgroup ProductActionGroup ∧
                ¬ TwoTransitivePermutationSubgroup ProductActionGroup ∧
                  DistinctHammingOrbitals

end MathlibPlus.Open.Research.R1162

namespace MathlibPlus.Open.Research.R1162

def claim41484 : Prop :=
  Fintype.card ProductActionPoints = 729 ∧
    (∀ b : BaseNine, Equiv.addRight b ∈ alternatingGroup BaseNine) ∧
      TranslationSubgroup ≤ ProductActionGroup ∧
        Nonempty (TranslationSubgroup ≃* C3SquaredCubed) ∧
          RegularPermutationSubgroup TranslationSubgroup ∧
            (∀ t : ProductActionPoints, t ≠ 0 →
              ∀ v : ProductActionPoints,
                (Translation t : Equiv.Perm ProductActionPoints) v ≠ v) ∧
              PrimitivePermutationSubgroup ProductActionGroup ∧
                ¬ TwoTransitivePermutationSubgroup ProductActionGroup ∧
                  DistinctHammingOrbitals

end MathlibPlus.Open.Research.R1162
