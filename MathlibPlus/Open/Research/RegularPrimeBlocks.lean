import Mathlib

namespace MathlibPlus.Open.Research.RegularPrimeBlocks

abbrev Perm (Ω : Type*) := Equiv.Perm Ω

def IsRegularPermutationSubgroup {Ω : Type*} [Fintype Ω]
    (R : Subgroup (Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! r : R, (r : Perm Ω) x = y

def IsAbelianPermutationSubgroup {Ω : Type*}
    (R : Subgroup (Perm Ω)) : Prop :=
  ∀ r s : R, (r : Perm Ω) * (s : Perm Ω) = (s : Perm Ω) * (r : Perm Ω)

def IsPermutationPGroup {Ω : Type*} [Fintype Ω]
    (p : ℕ) (R : Subgroup (Perm Ω)) : Prop :=
  ∀ r : R, ∃ k : ℕ, orderOf (r : Perm Ω) = p ^ k

def generatedPermutationGroup {Ω : Type*}
    (R T : Subgroup (Perm Ω)) : Subgroup (Perm Ω) :=
  Subgroup.closure ((R : Set (Perm Ω)) ∪ (T : Set (Perm Ω)))

def centerInPermutationGroup {Ω : Type*}
    (P : Subgroup (Perm Ω)) : Set (Perm Ω) :=
  {z | z ∈ P ∧ ∀ y : Perm Ω, y ∈ P → z * y = y * z}

def conjugateMembership {Ω : Type*}
    (T : Subgroup (Perm Ω)) (x z : Perm Ω) : Prop :=
  ∃ t : T, z = x⁻¹ * (t : Perm Ω) * x

def isSylowPermutationSubgroup {Ω : Type*} [Fintype Ω]
    (p : ℕ) (X P : Subgroup (Perm Ω)) : Prop :=
  P ≤ X ∧ IsPermutationPGroup p P ∧
    ∀ Q : Subgroup (Perm Ω), Q ≤ X → IsPermutationPGroup p Q → Nat.card Q ≤ Nat.card P

/-- Claim 29942: after conjugating one regular elementary abelian copy into a
common Sylow subgroup, that Sylow subgroup has a nontrivial central subgroup
inside both copies. -/
def commonCentralPrimeSubgroupAfterSylowReductionClaim
    {Ω : Type*} [Fintype Ω] (p : ℕ)
    (R T : Subgroup (Perm Ω)) : Prop :=
  Nat.Prime p ∧
    IsRegularPermutationSubgroup R ∧ IsRegularPermutationSubgroup T ∧
    IsAbelianPermutationSubgroup R ∧ IsAbelianPermutationSubgroup T ∧
    IsPermutationPGroup p R ∧ IsPermutationPGroup p T →
      let X := generatedPermutationGroup R T
      ∃ x : Perm Ω, x ∈ X ∧
        ∃ P : Subgroup (Perm Ω),
          isSylowPermutationSubgroup p X P ∧
            (∀ r : R, (r : Perm Ω) ∈ P) ∧
            (∀ t : T, x⁻¹ * (t : Perm Ω) * x ∈ P) ∧
            (∃ z : Perm Ω, z ∈ centerInPermutationGroup P ∧ z ≠ 1) ∧
            (∀ z : Perm Ω, z ∈ centerInPermutationGroup P →
              z ∈ R ∧ conjugateMembership T x z)

/-- The centralizer of a permutation subgroup in the full symmetric group. -/
def centralizerInSymmetricGroup {Ω : Type*}
    (R : Subgroup (Perm Ω)) : Set (Perm Ω) :=
  {g | ∀ r : Perm Ω, r ∈ R → g * r = r * g}

/-- Claim 29943: the center centralizes the regular abelian copy, whose full
symmetric-group centralizer is that copy itself. -/
def centerOfSylowLiesInRegularCopyClaim
    {Ω : Type*} [Fintype Ω] (p : ℕ)
    (P R : Subgroup (Perm Ω)) : Prop :=
  IsPermutationPGroup p P ∧ R ≤ P ∧
    IsRegularPermutationSubgroup R ∧ IsAbelianPermutationSubgroup R →
      (∀ z : Perm Ω, z ∈ centerInPermutationGroup P →
        ∀ r : Perm Ω, r ∈ R → z * r = r * z) ∧
      centralizerInSymmetricGroup R = (R : Set (Perm Ω)) ∧
      (∀ z : Perm Ω, z ∈ centerInPermutationGroup P → z ∈ R)

end MathlibPlus.Open.Research.RegularPrimeBlocks
