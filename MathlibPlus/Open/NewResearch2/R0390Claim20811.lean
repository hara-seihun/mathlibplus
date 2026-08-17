import MathlibPlus.Open.NewResearch2.R0390AtomisticClosure

namespace MathlibPlus.Open.NewResearch2.R0390Claim20811

open scoped BigOperators
open Classical

noncomputable section

abbrev Lattice61 := MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.closureLattice

/-- The three tight coordinates and the outside target coordinate, represented
by their eight-bit masks. -/
def tightMask : ℕ := 7
def targetMask : ℕ := 8
def outsideMask : ℕ := Nat.xor 255 tightMask
def coordinateMask (i : Fin 8) : ℕ := 2 ^ i.val
def tightCoordinates : Finset ℕ := {1, 2, 4}

def maskSupport (x : ℕ) : Finset (Fin 8) :=
  Finset.univ.filter (fun i =>
    MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below
      (coordinateMask i) x)

def latticeBelow (x y : ℕ) : Prop :=
  x ∈ Lattice61 ∧ y ∈ Lattice61 ∧
    MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below x y

def strictLatticeBelow (x y : ℕ) : Prop :=
  latticeBelow x y ∧ x ≠ y

/-- Cover sets are computed in the displayed 61-element closure lattice, not
in an unrelated abstract order. -/
def lowerCoverSet (x : ℕ) : Finset ℕ :=
  let _ : DecidablePred (fun y : ℕ =>
      y ≠ x ∧ MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below y x ∧
        ¬ ∃ z ∈ Lattice61,
          z ≠ y ∧ z ≠ x ∧
          MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below y z ∧
          MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below z x) :=
    Classical.decPred _
  Lattice61.filter (fun y =>
    y ≠ x ∧ MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below y x ∧
      ¬ ∃ z ∈ Lattice61,
        z ≠ y ∧ z ≠ x ∧
        MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below y z ∧
        MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below z x)

def upperCoverSet (x : ℕ) : Finset ℕ :=
  let _ : DecidablePred (fun y : ℕ =>
      y ≠ x ∧ MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below x y ∧
        ¬ ∃ z ∈ Lattice61,
          z ≠ y ∧ z ≠ x ∧
          MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below x z ∧
          MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below z y) :=
    Classical.decPred _
  Lattice61.filter (fun y =>
    y ≠ x ∧ MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below x y ∧
      ¬ ∃ z ∈ Lattice61,
        z ≠ y ∧ z ≠ x ∧
        MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below x z ∧
        MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below z y)

def meetIrreducibleMask (x : ℕ) : Prop :=
  x ∈ Lattice61 ∧ x ≠ 255 ∧ (upperCoverSet x).card = 1

def meetIrreducibles : Finset ℕ :=
  let _ : DecidablePred meetIrreducibleMask := Classical.decPred _
  Lattice61.filter meetIrreducibleMask

def principalFilterSize (j : ℕ) : ℕ :=
  (Lattice61.filter (fun x =>
    MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below j x)).card

def joinIrreduciblesBelow (x : ℕ) : Finset ℕ :=
  MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.joinIrreducibleMasks.filter
    (fun j =>
      MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below j x)

def transportedEdge (S : ℕ) : Finset ℕ :=
  (joinIrreduciblesBelow
      (MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.joinMask targetMask S)) \
    (joinIrreduciblesBelow
      (MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.joinMask 0 S))

def pureTransportAt (S : ℕ) : Prop :=
  transportedEdge S = ({targetMask} : Finset ℕ)

def tightCube : Finset ℕ := Finset.range 8
def properTightCube : Finset ℕ := (Finset.range 8).erase 7

def closureOfMask (x : ℕ) : ℕ :=
  MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.intersectionMask
    (Lattice61.filter (fun g =>
      MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below x g))

def canonicalTightCube : Finset ℕ :=
  (Finset.range 8).image (fun S =>
    MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.joinMask targetMask S)

def canonicalTightTraces : Finset ℕ :=
  canonicalTightCube.image (fun x => Nat.land x tightMask)

/-- The complementary family is the actual bitwise complement of the same
61-element closure lattice. -/
def complementaryFamily : Finset ℕ :=
  Lattice61.image (fun x => Nat.xor 255 x)

def familyCoordinatePresent (A : ℕ) (i : Fin 8) : Prop :=
  MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below
    (coordinateMask i) A

def familyFrequency (i : Fin 8) : ℕ :=
  (complementaryFamily.filter (fun A => familyCoordinatePresent A i)).card

def familyDeficit (i : Fin 8) : ℤ :=
  (complementaryFamily.card : ℤ) - 2 * (familyFrequency i : ℤ)

def familyUnionClosed : Prop :=
  ∀ A ∈ complementaryFamily, ∀ B ∈ complementaryFamily,
    Nat.lor A B ∈ complementaryFamily

def familySeparating : Prop :=
  ∀ i j : Fin 8, i ≠ j →
    ∃ A ∈ complementaryFamily,
      (familyCoordinatePresent A i ∧ ¬ familyCoordinatePresent A j) ∨
      (¬ familyCoordinatePresent A i ∧ familyCoordinatePresent A j)

def familyNormalization : Prop :=
  complementaryFamily.card = 61 ∧
  (∀ A ∈ complementaryFamily, A = Nat.land A 255) ∧
  familyUnionClosed ∧
  (∀ A ∈ complementaryFamily,
    A ≠ 0 → 3 ≤ (maskSupport A).card) ∧
  (∀ i : Fin 8, ∃ A ∈ complementaryFamily,
    familyCoordinatePresent A i) ∧
  familySeparating ∧
  (∀ i : Fin 8,
    Nat.xor 255 (coordinateMask i) ∈ complementaryFamily)

def maskIntersection (S : Finset ℕ) : ℕ :=
  S.toList.foldl Nat.land 255

def tightFiber (trace : ℕ) : Finset ℕ :=
  (complementaryFamily.filter (fun A => Nat.land A tightMask = trace)).image
    (fun A => Nat.land A outsideMask)

def unionImage (A B : Finset ℕ) : Finset ℕ :=
  A.biUnion (fun a => B.image (fun b => Nat.lor a b))

def singletonFiberFactorization : Prop :=
  0 ∉ tightFiber 1 ∧
  0 ∉ tightFiber 2 ∧
  0 ∉ tightFiber 4 ∧
  tightFiber 3 = unionImage (tightFiber 1) (tightFiber 2) ∧
  tightFiber 5 = unionImage (tightFiber 1) (tightFiber 4) ∧
  tightFiber 6 = unionImage (tightFiber 2) (tightFiber 4) ∧
  tightFiber 7 =
    unionImage (unionImage (tightFiber 1) (tightFiber 2)) (tightFiber 4)

def emptyIntersectionInNonemptyTightFibers : Prop :=
  ∀ trace ∈ (Finset.range 8).erase 0,
    maskIntersection (tightFiber trace) = 0

def baseAbsorption : Prop :=
  unionImage (tightFiber 0) (tightFiber 1) = tightFiber 1 ∧
  unionImage (tightFiber 0) (tightFiber 2) = tightFiber 2 ∧
  unionImage (tightFiber 0) (tightFiber 4) = tightFiber 4

def removableMember (A : ℕ) : Prop :=
  A ∈ complementaryFamily ∧
    ∀ B ∈ complementaryFamily.erase A, ∀ C ∈ complementaryFamily.erase A,
      Nat.lor B C ∈ complementaryFamily.erase A

def removableMembers : Finset ℕ :=
  let _ : DecidablePred removableMember := Classical.decPred _
  complementaryFamily.filter removableMember

def removableSingletonTraceKernels : Prop :=
  0 ∈ removableMembers ∧
  (removableMembers.erase 0).image (fun A => Nat.xor 255 A) = meetIrreducibles ∧
  maskIntersection
      (removableMembers.filter (fun A => Nat.land A tightMask = 1)) = 1 ∧
  maskIntersection
      (removableMembers.filter (fun A => Nat.land A tightMask = 2)) = 2 ∧
  maskIntersection
      (removableMembers.filter (fun A => Nat.land A tightMask = 4)) = 4

def expectedFrequency (i : Fin 8) : ℕ :=
  match i.val with
  | 0 => 30
  | 1 => 30
  | 2 => 30
  | 3 => 29
  | 4 => 49
  | 5 => 49
  | 6 => 46
  | 7 => 45
  | _ => 0

def expectedDeficit (i : Fin 8) : ℤ :=
  match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => -37
  | 5 => -37
  | 6 => -31
  | 7 => -29
  | _ => 0

def targetFilterAndDeficitData : Prop :=
  principalFilterSize 1 = 31 ∧
  principalFilterSize 2 = 31 ∧
  principalFilterSize 4 = 31 ∧
  principalFilterSize targetMask = 32 ∧
  (∀ i : Fin 8, familyFrequency i = expectedFrequency i) ∧
  (∀ i : Fin 8, familyDeficit i = expectedDeficit i) ∧
  familyDeficit (3 : Fin 8) = 3

def completeMissingTightCoverClasses : Prop :=
  (∀ m ∈ meetIrreducibles,
    2 ≤ (maskSupport (Nat.land m tightMask)).card) ∧
  (∀ missing : Fin 3,
    let missingMask := 2 ^ missing.val
    let otherTight := Nat.xor tightMask missingMask
    (meetIrreducibles.filter (fun m =>
      Nat.land m tightMask = otherTight)).card =
      if missing.val = 1 then 3 else 4) ∧
  (∀ missing : Fin 3,
    let missingMask := 2 ^ missing.val
    let coverClass := meetIrreducibles.filter (fun m =>
      Nat.land m tightMask = Nat.xor tightMask missingMask)
    ∀ i : Fin 8, i.val ≠ missing.val →
      ∃ m ∈ coverClass,
        MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below
          (coordinateMask i) m)

def noMeetBelowJoin : Prop :=
  ∀ m ∈ meetIrreducibles,
    ∀ j ∈ MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.joinIrreducibleMasks,
      ¬ MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below m j

def noDoublyIrreducible : Prop :=
  ∀ m ∈ meetIrreducibles,
    m ∉ MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.joinIrreducibleMasks

def strictMajorityCondition : Prop :=
  ∀ Q : Finset ℕ,
    Q ⊆ meetIrreducibles → Q.Nonempty →
      ∃ j ∈ MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.joinIrreducibleMasks,
        2 * (Q.filter (fun m =>
          MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below j m)).card > Q.card

def exactHalfCondition : Prop :=
  ∀ m ∈ meetIrreducibles,
    ∃ j ∈ tightCoordinates,
      MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below j m ∧
      principalFilterSize j = (Lattice61.card + 1) / 2

def incomparableCount (x : ℕ) : ℕ :=
  (Lattice61.filter (fun y =>
    y ≠ x ∧
    ¬ MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below x y ∧
    ¬ MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.below y x)).card

def minimumLatticeConditions : Prop :=
  Lattice61.card ≥ 53 ∧
  noMeetBelowJoin ∧
  noDoublyIrreducible ∧
  strictMajorityCondition ∧
  exactHalfCondition ∧
  (∀ x ∈ Lattice61, x ≠ 0 → x ≠ 255 → 3 ≤ incomparableCount x)

def targetTransportProfile : Prop :=
  targetMask ∈
      MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.joinIrreducibleMasks ∧
  lowerCoverSet targetMask = ({0} : Finset ℕ) ∧
  (∀ S ∈ properTightCube, transportedEdge S = ({targetMask} : Finset ℕ)) ∧
  transportedEdge tightMask = (∅ : Finset ℕ) ∧
  closureOfMask tightMask = Nat.lor tightMask targetMask ∧
  closureOfMask (Nat.lor tightMask targetMask) =
    Nat.lor tightMask targetMask

def canonicalCubeSurvives : Prop :=
  canonicalTightCube.card = 8 ∧
  canonicalTightTraces = Finset.range 8

def localTransportPremise : Prop :=
  completeMissingTightCoverClasses ∧
  exactHalfCondition ∧
  3 ≤ familyDeficit (3 : Fin 8) ∧
  familyNormalization ∧
  singletonFiberFactorization ∧
  baseAbsorption ∧
  emptyIntersectionInNonemptyTightFibers ∧
  removableSingletonTraceKernels ∧
  minimumLatticeConditions

/-- Claim 20811.  This is one concrete counterexample: all cover, exact-half,
deficit, normalization, and minimum-lattice premises are attached to the
same 61-element closure lattice and its complementary family, while the
specific lower-cover transport is pure at exactly the seven proper tight
positions and collapses at the top. -/
def localLowerCoverTransportImplicationIsFalse_claim20811 : Prop :=
  localTransportPremise ∧
  targetFilterAndDeficitData ∧
  canonicalCubeSurvives ∧
  targetTransportProfile ∧
  ¬ (localTransportPremise →
    ∀ S ∈ tightCube,
      transportedEdge S = ({targetMask} : Finset ℕ))

end

end MathlibPlus.Open.NewResearch2.R0390Claim20811
