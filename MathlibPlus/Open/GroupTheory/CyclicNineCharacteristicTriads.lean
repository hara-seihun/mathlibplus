import Mathlib

namespace MathlibPlus.Open.GroupTheory

abbrev NinePoints := Fin 9
abbrev PermutationNine := Equiv.Perm NinePoints

/-- A subgroup of the degree-nine symmetric group is a regular cyclic group of
order nine when it has a generator of order nine and its action is regular. -/
def regularCyclicNine (R : Subgroup PermutationNine) : Prop :=
  Nat.card R = 9 ∧
    (∃ g : R, orderOf g = 9) ∧
    ∀ x y : NinePoints, ∃! r : R, (r : PermutationNine) x = y

/-- The characteristic order-three part, written without choosing a generator. -/
def omegaOne (R : Subgroup PermutationNine) : Set PermutationNine :=
  {r | r ∈ R ∧ r ^ 3 = 1}

def orbitOf (K : Set PermutationNine) (x : NinePoints) : Set NinePoints :=
  {y | ∃ r, r ∈ K ∧ r x = y}

def orbitPartition (K : Set PermutationNine) : Set (Set NinePoints) :=
  {B | ∃ x, B = orbitOf K x}

/-- The orbit sets are exactly three pairwise disjoint blocks, each of size
three, and cover the nine points. -/
def threeBlockPartition (K : Set PermutationNine) : Prop :=
  (∀ x : NinePoints, (orbitOf K x).ncard = 3) ∧
    (∀ x y : NinePoints,
      orbitOf K x = orbitOf K y ∨ Disjoint (orbitOf K x) (orbitOf K y)) ∧
    (∀ y : NinePoints, ∃ x : NinePoints, y ∈ orbitOf K x) ∧
    (∃ x₁ x₂ x₃ : NinePoints,
      orbitOf K x₁ ≠ orbitOf K x₂ ∧
      orbitOf K x₁ ≠ orbitOf K x₃ ∧
      orbitOf K x₂ ≠ orbitOf K x₃ ∧
      ∀ x : NinePoints,
        orbitOf K x = orbitOf K x₁ ∨
          orbitOf K x = orbitOf K x₂ ∨
          orbitOf K x = orbitOf K x₃)

/-- Claim 39412: the order-three elements of a regular cyclic-nine action form
its unique subgroup of order three, and their orbits are the characteristic
triad partition. -/
def characteristicTriadPartitionCyclicNine : Prop :=
  ∀ R : Subgroup PermutationNine,
    regularCyclicNine R →
      ∃ Ω : Subgroup PermutationNine,
        Ω ≤ R ∧
          Nat.card Ω = 3 ∧
          (Ω : Set PermutationNine) = omegaOne R ∧
          (∀ K : Subgroup PermutationNine,
            K ≤ R → Nat.card K = 3 → K = Ω) ∧
          (∀ φ : R ≃* R, ∀ r : R,
            ((r : PermutationNine) ∈ Ω ↔ (φ r : PermutationNine) ∈ Ω)) ∧
          threeBlockPartition (Ω : Set PermutationNine)

/-- Transitivity of a subgroup in its given degree-nine permutation action. -/
def transitiveNine (X : Subgroup PermutationNine) : Prop :=
  ∀ x y : NinePoints, ∃ g : X, (g : PermutationNine) x = y

/-- Conjugating the characteristic order-three set by a permutation. -/
def conjugatedOmega (T : Subgroup PermutationNine) (x : PermutationNine) :
    Set PermutationNine :=
  {p | ∃ t, t ∈ omegaOne T ∧ p = x⁻¹ * t * x}

/-- Claim 39413: in a transitive ambient degree-nine group, regular cyclic-nine
subgroups have characteristic triad partitions aligned by an ambient element. -/
def characteristicTriadAmbientAlignment : Prop :=
  ∀ (X R T : Subgroup PermutationNine),
    transitiveNine X →
      regularCyclicNine R →
        regularCyclicNine T →
          R ≤ X →
            T ≤ X →
              ∃ x : X,
                orbitPartition (omegaOne R) =
                  orbitPartition (conjugatedOmega T (x : PermutationNine))

end MathlibPlus.Open.GroupTheory
