import Mathlib

namespace MathlibPlus.Open.R1081

abbrev Z7 := ZMod 7

/-- The two seven-vertex connection sets occurring in the factor graphs. -/
def factorSteps : Fin 2 → Set Z7
  | 0 => {1, -1}
  | 1 => {1, -1, 2, -2}

/-- Adjacency in a cyclic Cayley graph with a displayed connection set. -/
def cyclicAdj (steps : Set Z7) (x y : Z7) : Prop := y - x ∈ steps

/-- The affine realization of the dihedral group of order 14 on `C₇`. -/
def dihedralPermutation (σ : Equiv.Perm Z7) : Prop :=
  ∃ c : Z7, ∃ ε : Z7, (ε = 1 ∨ ε = -1) ∧ ∀ x : Z7, σ x = ε * x + c

/-- A permutation is an automorphism of the displayed cyclic Cayley graph. -/
def cyclicGraphAut (steps : Set Z7) (σ : Equiv.Perm Z7) : Prop :=
  ∀ x y : Z7, cyclicAdj steps (σ x) (σ y) ↔ cyclicAdj steps x y

/-- Both factor graphs have precisely the affine dihedral automorphisms. -/
def factorGraphAutomorphismGroups : Prop :=
  ∀ i : Fin 2, ∀ σ : Equiv.Perm Z7,
    cyclicGraphAut (factorSteps i) σ ↔ dihedralPermutation σ

/-- The four connection sets on `C₇²` from the stated `Q,I` choices. -/
def kernelConnectionSet (Q I : Set Z7) : Set (Z7 × Z7) :=
  {p | (p.1 = 0 ∧ p.2 ∈ I) ∨ p.1 ∈ Q}

/-- Adjacency in the Cayley graph on `C₇²` with connection set `X_{Q,I}`. -/
def kernelAdj (Q I : Set Z7) (p r : Z7 × Z7) : Prop :=
  (r.1 - p.1, r.2 - p.2) ∈ kernelConnectionSet Q I

/-- The permutations obtained by an outer affine action and an independent
inner affine action on each of the seven fibers. -/
def wreathDihedralPermutation (σ : Equiv.Perm (Z7 × Z7)) : Prop :=
  ∃ c : Z7, ∃ ε : Z7, (ε = 1 ∨ ε = -1) ∧
    ∀ x : Z7, ∃ d : Z7, ∃ ρ : Z7, (ρ = 1 ∨ ρ = -1) ∧
      ∀ y : Z7, σ (x, y) = (ε * x + c, ρ * y + d)

/-- A permutation is an automorphism of the displayed kernel Cayley graph. -/
def kernelGraphAut (Q I : Set Z7) (σ : Equiv.Perm (Z7 × Z7)) : Prop :=
  ∀ p r : Z7 × Z7, kernelAdj Q I (σ p) (σ r) ↔ kernelAdj Q I p r

/-- The four explicit `Q,I` choices. -/
def admissibleQI (Q I : Set Z7) : Prop :=
  (Q = ({1, -1} : Set Z7) ∨ Q = ({1, -1, 2, -2} : Set Z7)) ∧
  (I = ({1, -1} : Set Z7) ∨ I = ({1, -1, 2, -2} : Set Z7))

/-- Full wreath-product automorphism group and the two stated orders for every
one of the four explicit kernel graphs. -/
def kernelGraphAutomorphismGroups : Prop :=
  ∀ Q I : Set Z7, admissibleQI Q I →
    (∀ σ : Equiv.Perm (Z7 × Z7),
      kernelGraphAut Q I σ ↔ wreathDihedralPermutation σ) ∧
    Nat.card {σ : Equiv.Perm (Z7 × Z7) // kernelGraphAut Q I σ} = 14 ^ 8 ∧
    Nat.card {σ : Equiv.Perm (Z7 × Z7) //
      kernelGraphAut Q I σ ∧ σ (0, 0) = (0, 0)} = 2 * 2 * 14 ^ 6

end MathlibPlus.Open.R1081
