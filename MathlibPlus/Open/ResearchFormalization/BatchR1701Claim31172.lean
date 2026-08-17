import Mathlib
import MathlibPlus.Open.ResearchFormalization.MinimumBlockAction

namespace MathlibPlus.Open.ResearchFormalization.R1701Claim31172

abbrev Perm (Ω : Type*) := Equiv.Perm Ω

abbrev C2PowTimesC9 (r : ℕ) :=
  Multiplicative (Fin r → ZMod 2) × Multiplicative (ZMod 9)

def transitivePermutationSubgroup {Ω : Type*}
    (X : Subgroup (Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃ g : X, (g : Perm Ω) x = y

def regularPermutationSubgroup {Ω : Type*} [Fintype Ω]
    (R : Subgroup (Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! r : R, (r : Perm Ω) x = y

def regularC2PowTimesC9Copy {Ω : Type*} [Fintype Ω]
    (r : ℕ) (R : Subgroup (Perm Ω)) : Prop :=
  Nonempty (C2PowTimesC9 r ≃* R) ∧
    regularPermutationSubgroup R

def omegaOneOThreeOfSet {Ω : Type*}
    (D : Set (Perm Ω)) : Set (Perm Ω) :=
  {p | p ∈ D ∧ p ^ 3 = 1}

def orbitOfPermutationSet {Ω : Type*}
    (D : Set (Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ p : Perm Ω, p ∈ D ∧ p x = y}

def orbitPartitionOfPermutationSet {Ω : Type*}
    (D : Set (Perm Ω)) : Set (Set Ω) :=
  {B | ∃ x : Ω, B = orbitOfPermutationSet D x}

def conjugatedPermutationSet {Ω : Type*}
    (T : Subgroup (Perm Ω)) (δ : Perm Ω) : Set (Perm Ω) :=
  {p | ∃ t : T, p = δ⁻¹ * (t : Perm Ω) * δ}

def fixesBlockSystem {Ω : Type*}
    (𝓑 : Set (Set Ω)) (δ : Perm Ω) : Prop :=
  ∀ B : Set Ω, B ∈ 𝓑 → δ '' B = B

def threePointPartition {Ω : Type*}
    (𝓟 : Set (Set Ω)) : Prop :=
  ∀ B : Set Ω, B ∈ 𝓟 → B.ncard = 3

def generatedByPermutationSet {Ω : Type*}
    (R : Subgroup (Perm Ω)) (T : Set (Perm Ω)) : Subgroup (Perm Ω) :=
  Subgroup.closure ((R : Set (Perm Ω)) ∪ T)

def generatedPairPreservesPartition {Ω : Type*}
    (R : Subgroup (Perm Ω)) (T : Set (Perm Ω)) (𝓟 : Set (Set Ω)) : Prop :=
  ∀ g : generatedByPermutationSet R T, ∀ B : Set Ω,
    B ∈ 𝓟 → (g : Perm Ω) '' B ∈ 𝓟

def divisibleByThreeBlockSystem {Ω : Type*}
    (𝓑 : Set (Set Ω)) : Prop :=
  ∀ B : Set Ω, B ∈ 𝓑 → 3 ∣ B.ncard

/-- Claim 31172: the retained descent is scoped to ranks two and three, all
minimum nontrivial block systems with block size divisible by three, and
arbitrary finite transitive permutation overgroups.  The common partition is
formed from the order-three characteristic elements of both regular copies,
not from the whole conjugated regular target.  Its conclusion stops at common
three-point triads invariant under the generated pair: it contains no
orientation of characteristic lines, no pure-binary block branch, and no
presentation-level quotient/fiber induction or generated-image quotient
conjugator. -/
def claim31172 : Prop :=
  ∀ (r : ℕ), (r = 2 ∨ r = 3) →
    ∀ (Ω : Type*) [Fintype Ω]
      (X : Subgroup (Perm Ω)),
      transitivePermutationSubgroup X →
      ∀ R T : Subgroup (Perm Ω),
        R ≤ X → T ≤ X →
        regularC2PowTimesC9Copy r R →
        regularC2PowTimesC9Copy r T →
        ∀ 𝓑 : Set (Set Ω),
          MathlibPlus.Open.ResearchFormalization.minimumNontrivialBlockSystem
            (X : Set (Perm Ω)) 𝓑 →
          divisibleByThreeBlockSystem 𝓑 →
          ∃ δ : X,
            fixesBlockSystem 𝓑 (δ : Perm Ω) ∧
            let Tδ : Set (Perm Ω) :=
              conjugatedPermutationSet T (δ : Perm Ω)
            let PR : Set (Set Ω) :=
              orbitPartitionOfPermutationSet
                (omegaOneOThreeOfSet (R : Set (Perm Ω)))
            let PT : Set (Set Ω) :=
              orbitPartitionOfPermutationSet
                (omegaOneOThreeOfSet Tδ)
            PR = PT ∧
              threePointPartition PR ∧
              generatedPairPreservesPartition R Tδ PR

end MathlibPlus.Open.ResearchFormalization.R1701Claim31172
