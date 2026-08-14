import Mathlib

namespace MathlibPlus.Open.Research.CentralizerOrbit

abbrev Perm (Ω : Type*) := Equiv.Perm Ω

def isRegularPermutationSubgroup {Ω : Type*} [Fintype Ω]
    (R : Subgroup (Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! r : R, (r : Perm Ω) x = y

def isSemiregularPermutationSubgroup {Ω : Type*}
    (R : Subgroup (Perm Ω)) : Prop :=
  ∀ r : R, (r : Perm Ω) ≠ 1 → ∀ x : Ω, (r : Perm Ω) x ≠ x

def subgroupOrbit {Ω : Type*}
    (R : Subgroup (Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ r : R, (r : Perm Ω) x = y}

def subgroupOrbitFamily {Ω : Type*}
    (R : Subgroup (Perm Ω)) : Set (Set Ω) :=
  {B | ∃ x : Ω, B = subgroupOrbit R x}

def centralizesSubgroups {Ω : Type*}
    (Z E : Subgroup (Perm Ω)) : Prop :=
  ∀ z : Z, ∀ e : E,
    (z : Perm Ω) * (e : Perm Ω) = (e : Perm Ω) * (z : Perm Ω)

def isRegularOnOrbitFamily {Ω : Type*} [Fintype Ω]
    (E Z : Subgroup (Perm Ω)) : Prop :=
  ∀ B C : Set Ω, B ∈ subgroupOrbitFamily Z → C ∈ subgroupOrbitFamily Z →
    ∃! e : E, (e : Perm Ω) '' B = C

def generatedProductSubgroup {Ω : Type*}
    (Z E : Subgroup (Perm Ω)) : Subgroup (Perm Ω) :=
  Subgroup.closure ((Z : Set (Perm Ω)) ∪ (E : Set (Perm Ω)))

def isCharacteristicSubgroup {Ω : Type*}
    (Z T : Subgroup (Perm Ω)) : Prop :=
  ∀ φ : T ≃* T, ∀ z : T,
    ((z : Perm Ω) ∈ Z ↔ (φ z : Perm Ω) ∈ Z)

def isTransitivePermutationSubgroup {Ω : Type*}
    (R : Subgroup (Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃ r : R, (r : Perm Ω) x = y

/-- Claim 30141: the characteristic odd and Sylow-two factors of a regular
`C₂² × Cₘ` copy have the stated orbit and centralizer properties. -/
def characteristicFactorsOfRegularC2SquaredTimesCmClaim
    {Ω : Type*} [Fintype Ω] (m : ℕ)
    (Q T : Subgroup (Perm Ω)) : Prop :=
  0 < m ∧ Odd m ∧ T ≤ Q ∧ isRegularPermutationSubgroup T ∧
    Nonempty (T ≃* (Multiplicative (ZMod 2) ×
      Multiplicative (ZMod 2) × Multiplicative (ZMod m))) →
      ∃ Z E : Subgroup (Perm Ω),
        Z ≤ T ∧ E ≤ T ∧
          isCharacteristicSubgroup Z T ∧ isCharacteristicSubgroup E T ∧
          Nat.card Z = m ∧ IsCyclic Z ∧
          isSemiregularPermutationSubgroup Z ∧
          Set.ncard (subgroupOrbitFamily Z) = 4 ∧
          Nat.card E = 4 ∧
          (∀ e : E, (e : Perm Ω) ^ 2 = 1) ∧
          (∀ e₁ e₂ : E,
            (e₁ : Perm Ω) * (e₂ : Perm Ω) = (e₂ : Perm Ω) * (e₁ : Perm Ω)) ∧
          centralizesSubgroups Z E ∧ isRegularOnOrbitFamily E Z

/-- Claim 30142: a centralizing odd factor and a regular four-point elementary
factor assemble to a regular direct product. -/
def centralizerOrbitPairAssemblesRegularDirectProductClaim
    {Ω : Type*} [Fintype Ω] (m : ℕ)
    (Z E : Subgroup (Perm Ω)) : Prop :=
  Odd m ∧ Nat.card Z = m ∧ IsCyclic Z ∧
    Nat.card E = 4 ∧
      (∀ e : E, (e : Perm Ω) ^ 2 = 1) ∧
      (∀ e₁ e₂ : E,
        (e₁ : Perm Ω) * (e₂ : Perm Ω) = (e₂ : Perm Ω) * (e₁ : Perm Ω)) ∧
    isSemiregularPermutationSubgroup Z ∧
    Set.ncard (subgroupOrbitFamily Z) = 4 ∧
    centralizesSubgroups Z E ∧ isRegularOnOrbitFamily E Z →
      let ZE := generatedProductSubgroup Z E
      (∀ g : ZE, ∃ z : Z, ∃ e : E,
        (g : Perm Ω) = (z : Perm Ω) * (e : Perm Ω)) ∧
        Nat.card ZE = 4 * m ∧
        isTransitivePermutationSubgroup ZE ∧
        isRegularPermutationSubgroup ZE ∧
        Nonempty ((Z × E) ≃* ZE)

end MathlibPlus.Open.Research.CentralizerOrbit
