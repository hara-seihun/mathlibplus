import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0390AtomisticClosure

noncomputable section

/-- The eight-coordinate universe mask. -/
def universeMask : ℕ := 255

/-- The fifteen displayed generators of the intersection closure. -/
def generatorMasks : Finset ℕ :=
  {27, 31, 45, 47, 62, 70, 78, 79, 85, 99, 139, 143, 158, 163, 205}

/-- The bit-inclusion order on the eight-coordinate masks. -/
def below (x y : ℕ) : Prop :=
  Nat.land x y = x

/-- The intersection of a finite family of masks, with the empty intersection
being the full eight-coordinate mask. -/
def intersectionMask (S : Finset ℕ) : ℕ :=
  S.toList.foldl Nat.land universeMask

/-- The closure lattice generated under intersections by the fifteen masks. -/
def closureLattice : Finset ℕ :=
  generatorMasks.powerset.image intersectionMask

/-- The closed upper bounds of one mask in the generated lattice. -/
def closedUpperBounds (x : ℕ) : Finset ℕ :=
  let _ : DecidablePred (fun z : ℕ => below x z) := Classical.decPred _
  closureLattice.filter (fun z => below x z)

/-- The least closed upper bound in the generated intersection lattice. -/
def joinMask (x y : ℕ) : ℕ :=
  intersectionMask (closedUpperBounds (Nat.lor x y))

/-- The join of a finite family of lattice masks. -/
def joinOf (S : Finset ℕ) : ℕ :=
  intersectionMask
    (closedUpperBounds (S.toList.foldl Nat.lor 0))

/-- Join-irreducibility computed with the actual closure-lattice join. -/
def joinIrreducibleMask (x : ℕ) : Prop :=
  x ∈ closureLattice ∧ x ≠ 0 ∧
    ∀ a ∈ closureLattice, ∀ b ∈ closureLattice,
      joinMask a b = x → x = a ∨ x = b

/-- The eight singleton coordinate masks. -/
def singletonMasks : Finset ℕ :=
  {1, 2, 4, 8, 16, 32, 64, 128}

/-- The computed join-irreducible mask list. -/
def joinIrreducibleMasks : Finset ℕ :=
  let _ : DecidablePred joinIrreducibleMask := Classical.decPred _
  closureLattice.filter joinIrreducibleMask

/-- The singleton masks below a lattice element. -/
def singletonMasksBelow (x : ℕ) : Finset ℕ :=
  let _ : DecidablePred (fun a : ℕ => below a x) := Classical.decPred _
  singletonMasks.filter (fun a => below a x)

/-- The atom predicate in the actual finite closure lattice. -/
def atomMask (x : ℕ) : Prop :=
  x ∈ closureLattice ∧ x ≠ 0 ∧
    ∀ y ∈ closureLattice, below y x → y = 0 ∨ y = x

/-- Claim 20802: the explicitly generated intersection-closure lattice has
exactly 61 elements, is atomistic, and has exactly the eight singleton masks
as its join-irreducibles. -/
def claim20802 : Prop :=
  closureLattice.card = 61 ∧
  singletonMasks ⊆ closureLattice ∧
  (∀ x ∈ singletonMasks, atomMask x) ∧
  joinIrreducibleMasks = singletonMasks ∧
  (∀ x ∈ closureLattice,
    joinOf (singletonMasksBelow x) = x)

end

end MathlibPlus.Open.NewResearch2.R0390AtomisticClosure
