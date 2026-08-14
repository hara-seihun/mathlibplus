import Mathlib

namespace MathlibPlus.Open.ResearchBatchOrbitalPartition

noncomputable section

abbrev V3r (r : ℕ) := Fin r → ZMod 3
abbrev G4r (r : ℕ) := ZMod 4 × V3r r

def zeroV3 (r : ℕ) : V3r r := 0
def identity4 (r : ℕ) : G4r r := (0, zeroV3 r)

def completeFourPartiteAutomorphism (r : ℕ) (φ : G4r r → G4r r) : Prop :=
  Function.Bijective φ ∧
    ∀ u v, u.1 ≠ v.1 ↔ (φ u).1 ≠ (φ v).1

def pointStabilizerOrbit (r : ℕ) (x : G4r r) : Set (G4r r) :=
  {y | ∃ φ : G4r r → G4r r,
    completeFourPartiteAutomorphism r φ ∧ φ (identity4 r) = identity4 r ∧ φ x = y}

def pointStabilizerPartition (r : ℕ) : Set (Set (G4r r)) :=
  Set.range (pointStabilizerOrbit r)

def X0 (r : ℕ) : Set (G4r r) :=
  {identity4 r}

def X1 (r : ℕ) : Set (G4r r) :=
  {g | g.1 = 0 ∧ g.2 ≠ zeroV3 r}

def X2 (r : ℕ) : Set (G4r r) :=
  {g | g.1 ≠ 0}

def wreathPermutation4 (r : ℕ) (φ : G4r r → G4r r) : Prop :=
  ∃ σ : Equiv.Perm (ZMod 4),
    ∃ locals : ZMod 4 → Equiv.Perm (V3r r),
      ∀ g : G4r r, φ g = (σ g.1, locals g.1 g.2)

def wreathPermutationSet4 (r : ℕ) : Set (G4r r → G4r r) :=
  {φ | wreathPermutation4 r φ}

/-- The explicit three basic sets are the point-stabilizer orbits, and the
partwise-symmetric wreath permutations act as graph automorphisms. -/
def fourPartiteOrbitalPartitionClaim : Prop :=
  ∀ r : ℕ,
    pointStabilizerPartition r = {X0 r, X1 r, X2 r} ∧
      (∀ φ : G4r r → G4r r,
        φ ∈ wreathPermutationSet4 r → completeFourPartiteAutomorphism r φ)

end
end MathlibPlus.Open.ResearchBatchOrbitalPartition
