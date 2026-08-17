import Mathlib

namespace MathlibPlus.Open.Research.R1378

noncomputable section

abbrev A4 := alternatingGroup (Fin 4)
abbrev PrimeA4 (p : ℕ) := Multiplicative (ZMod p) × A4
abbrev V4 := Multiplicative (ZMod 2 × ZMod 2)

private def regularCopy (G : Type*) {Ω : Type*} [Group G]
    (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  Nonempty (R ≃* G) ∧
    ∀ x y : Ω, ∃! r : R, (r : Equiv.Perm Ω) x = y

private def semiregularV4 {Ω : Type*}
    (E : Subgroup (Equiv.Perm Ω)) : Prop :=
  Nonempty (E ≃* V4) ∧
    ∀ e : E, e ≠ 1 → ∀ x : Ω, (e : Equiv.Perm Ω) x ≠ x

private def normalIn {Ω : Type*}
    (E R : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ r : R, ∀ e : E,
    (r : Equiv.Perm Ω) * (e : Equiv.Perm Ω) *
        (r : Equiv.Perm Ω)⁻¹ ∈ E

private def orbit {Ω : Type*}
    (E : Subgroup (Equiv.Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ e : E, (e : Equiv.Perm Ω) x = y}

private def orbitPartition {Ω : Type*}
    (E : Subgroup (Equiv.Perm Ω)) : Set (Set Ω) :=
  {B | ∃ x : Ω, B = orbit E x}

private def conjugateSet {Ω : Type*}
    (δ : Equiv.Perm Ω) (T : Set (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) :=
  {g | ∃ t ∈ T, g = δ * t * δ⁻¹}

private def conjugatedOrbit {Ω : Type*}
    (δ : Equiv.Perm Ω) (E : Subgroup (Equiv.Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ e : E, (δ * (e : Equiv.Perm Ω) * δ⁻¹) x = y}

private def conjugatedOrbitPartition {Ω : Type*}
    (δ : Equiv.Perm Ω) (E : Subgroup (Equiv.Perm Ω)) : Set (Set Ω) :=
  {B | ∃ x : Ω, B = conjugatedOrbit δ E x}

private def isBlockSystemFor {Ω : Type*}
    (K : Set (Equiv.Perm Ω)) (P : Set (Set Ω)) : Prop :=
  P.Nonempty ∧
    ⋃₀ P = Set.univ ∧
    (∀ B ∈ P, B.Nonempty) ∧
    (∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) ∧
    (∀ g ∈ K, ∀ B ∈ P,
      ∃ C ∈ P, g '' B = C)

private def nontrivialBlockSystem {Ω : Type*}
    (P : Set (Set Ω)) : Prop :=
  P ≠ {Set.univ}

private def nonconjugateSetPair {Ω : Type*}
    (R : Set (Equiv.Perm Ω)) (T : Set (Equiv.Perm Ω)) : Prop :=
  ¬ ∃ α : Equiv.Perm Ω,
    ∀ r : Equiv.Perm Ω, r ∈ R ↔ α * r * α⁻¹ ∈ T

private def commonFourPointOrbitSystem {Ω : Type*}
    (R : Subgroup (Equiv.Perm Ω))
    (T : Set (Equiv.Perm Ω))
    (δ : Equiv.Perm Ω)
    (E_R E_T : Subgroup (Equiv.Perm Ω))
    (P : Set (Set Ω)) : Prop :=
  P = orbitPartition E_R ∧
    orbitPartition E_R = conjugatedOrbitPartition δ E_T ∧
    isBlockSystemFor (R : Set (Equiv.Perm Ω)) P ∧
    isBlockSystemFor (conjugateSet δ T) P ∧
    (∀ B ∈ P, Set.ncard B = 4) ∧
    nontrivialBlockSystem P

/-- Claim 38396: aligned semiregular V4 orbit partitions produce an actual
four-point block system for the generated nonconjugate pair; the residual
size-twelve block theorem then makes that support impossible. -/
def claim38396 : Prop :=
  ∀ (p : ℕ) (Ω : Type*) [Fintype Ω]
    (R T : Subgroup (Equiv.Perm Ω))
    (E_R E_T : Subgroup (Equiv.Perm Ω))
    (δ : Equiv.Perm Ω),
    (Nat.Prime p ∧ (p = 7 ∨ p = 11)) ∧
    regularCopy (PrimeA4 p) R ∧
    regularCopy (PrimeA4 p) T ∧
    E_R ≤ R ∧ E_T ≤ T ∧
    normalIn E_R R ∧ normalIn E_T T ∧
    semiregularV4 E_R ∧ semiregularV4 E_T ∧
    nonconjugateSetPair
      (R : Set (Equiv.Perm Ω))
      (conjugateSet δ (T : Set (Equiv.Perm Ω))) ∧
    let X : Subgroup (Equiv.Perm Ω) :=
      Subgroup.closure
        ((R : Set (Equiv.Perm Ω)) ∪
          conjugateSet δ (T : Set (Equiv.Perm Ω)))
    (∀ P : Set (Set Ω),
      isBlockSystemFor (X : Set (Equiv.Perm Ω)) P →
        nontrivialBlockSystem P →
        ∀ B ∈ P, Set.ncard B = 12) ∧
    orbitPartition E_R = conjugatedOrbitPartition δ E_T →
      (∃ P : Set (Set Ω),
        commonFourPointOrbitSystem R (T : Set (Equiv.Perm Ω))
          δ E_R E_T P ∧
          isBlockSystemFor
            (X : Set (Equiv.Perm Ω)) P) ∧
      False

end

end MathlibPlus.Open.Research.R1378
