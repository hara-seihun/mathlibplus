import Mathlib

namespace MathlibPlus.Open.Research.OrbitalCriteria

def conjugateSet {Ω : Type} (q : Equiv.Perm Ω)
    (K : Set (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) :=
  Set.image (fun h => q⁻¹ * h * q) K

def twoClosureOf {Ω : Type} (K : Set (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) :=
  {q | ∀ x y, ∃ k, k ∈ K ∧ q x = k x ∧ q y = k y}

def stabilizerOrbit {Ω : Type} (K : Set (Equiv.Perm Ω)) (α x : Ω) : Set Ω :=
  {y | ∃ k, k ∈ K ∧ k α = α ∧ k x = y}

def fixesStabilizerOrbits {Ω : Type} (q : Equiv.Perm Ω)
    (K : Set (Equiv.Perm Ω)) (α : Ω) : Prop :=
  ∀ x, Set.image q (stabilizerOrbit K α x) = stabilizerOrbit K α x

def transitiveSet {Ω : Type} (K : Set (Equiv.Perm Ω)) : Prop :=
  ∀ x y, ∃ k, k ∈ K ∧ k x = y

/-- The generated-conjugate-pair suborbit criterion. -/
def claim28017 : Prop :=
  ∀ (Ω : Type) (H : Subgroup (Equiv.Perm Ω))
    (q : Equiv.Perm Ω) (α : Ω),
    transitiveSet (H : Set (Equiv.Perm Ω)) →
    q α = α →
    let G : Subgroup (Equiv.Perm Ω) :=
      Subgroup.closure
        ((H : Set (Equiv.Perm Ω)) ∪ conjugateSet q (H : Set (Equiv.Perm Ω)))
    fixesStabilizerOrbits q (G : Set (Equiv.Perm Ω)) α →
      q ∈ twoClosureOf (G : Set (Equiv.Perm Ω)) ∧
      ∃ c : Equiv.Perm Ω,
        c ∈ twoClosureOf (G : Set (Equiv.Perm Ω)) ∧
        Set.image (fun h => c⁻¹ * h * c) (H : Set (Equiv.Perm Ω)) =
          conjugateSet q (H : Set (Equiv.Perm Ω))

def translationSet {Ω : Type} [AddGroup Ω] : Set (Equiv.Perm Ω) :=
  Set.range (Equiv.addRight : Ω → Equiv.Perm Ω)

def differenceSuborbit {Ω : Type} [AddGroup Ω]
    (G : Subgroup (Equiv.Perm Ω)) (d : Ω) : Set Ω :=
  {u | ∃ g, g ∈ (G : Set (Equiv.Perm Ω)) ∧ g 0 = 0 ∧ g d = u}

def directedOrbital {Ω : Type} [AddGroup Ω]
    (G : Subgroup (Equiv.Perm Ω)) (x y : Ω) : Set (Ω × Ω) :=
  {p | ∃ g, g ∈ (G : Set (Equiv.Perm Ω)) ∧ g x = p.1 ∧ g y = p.2}

def preservesDirectedOrbitals {Ω : Type} [AddGroup Ω]
    (q : Equiv.Perm Ω) (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y,
    Set.image (fun p : Ω × Ω => (q p.1, q p.2)) (directedOrbital G x y) =
      directedOrbital G x y

def preservesDifferenceSuborbits {Ω : Type} [AddGroup Ω]
    (q : Equiv.Perm Ω) (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ d, Set.image q (differenceSuborbit G d) = differenceSuborbit G d

/-- Orbital colors for a regular translation group are the difference suborbits. -/
def claim28022 : Prop :=
  ∀ (Ω : Type) [AddGroup Ω] (G : Subgroup (Equiv.Perm Ω)),
    translationSet ⊆ (G : Set (Equiv.Perm Ω)) →
      (∀ x y,
        directedOrbital G x y =
          {p | p.2 - p.1 ∈ differenceSuborbit G (y - x)}) ∧
      (∀ q : Equiv.Perm Ω, q 0 = 0 →
        (preservesDirectedOrbitals q G ↔ preservesDifferenceSuborbits q G))

end MathlibPlus.Open.Research.OrbitalCriteria
