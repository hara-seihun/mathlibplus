import Mathlib

namespace MathlibPlus.Algebra.Claim43805

open scoped BigOperators

abbrev F := ZMod 13

def hOrbit (a : F) : Finset F :=
  {a, a * 3, a * 3 ^ 2}

def orbitRepresentatives : Finset F := {0, 1, 2, 4, 8}

def scaleByThree (B : Finset F) : Finset F :=
  B.image (fun x => (3 : F) * x)

def isUnionOfListedHOrbits (B : Finset F) : Prop :=
  ∃ S : Finset F, S ⊆ orbitRepresentatives ∧ S.biUnion hOrbit = B

def stableSupport (B : Finset F) : Prop := scaleByThree B = B

def rawNonemptyProperStableSupportCount : Nat :=
  ((Finset.univ : Finset (Finset F)).filter
    (fun B => scaleByThree B = B ∧ B.Nonempty ∧ B ≠ Finset.univ)).card

def multiplySupport (u : F) (B : Finset F) : Finset F :=
  B.image (fun x => u * x)

def supportCode (B : Finset F) : Nat :=
  B.sum (fun x => 2 ^ x.val)

def nonzeroScalars : Finset F :=
  Finset.univ.filter (fun u : F => u ≠ 0)

def isNormalizedStableSupport (B : Finset F) : Prop :=
  stableSupport B ∧ B.Nonempty ∧ B ≠ Finset.univ ∧
    ∀ u ∈ nonzeroScalars, supportCode B ≤ supportCode (multiplySupport u B)

def normalizedStableSupports : Finset (Finset F) :=
  (Finset.univ : Finset (Finset F)).filter
    (fun B => scaleByThree B = B ∧ B.Nonempty ∧ B ≠ Finset.univ ∧
      ∀ u ∈ nonzeroScalars, supportCode B ≤ supportCode (multiplySupport u B))

def supportOrbit (B : Finset F) : Finset (Finset F) :=
  nonzeroScalars.image (fun u => multiplySupport u B)

def supportOrbitSize (B : Finset F) : Nat := (supportOrbit B).card

def normalizedOrbitSizeCount (k : Nat) : Nat :=
  (normalizedStableSupports.filter (fun B => supportOrbitSize B = k)).card

end MathlibPlus.Algebra.Claim43805
