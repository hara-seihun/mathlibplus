import Mathlib
import MathlibPlus.Combinatorics.BooleanComponentSeparation

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Combinatorics.R2665BooleanMasks

abbrev Ground := Fin 5
abbrev Mask := ℕ

def maskSet (m : Mask) : Finset Ground :=
  Finset.univ.filter (fun i => Nat.testBit m i.val = true)

def unionClosed (F : Finset (Finset Ground)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

def coreFamily : Finset Mask := {0, 7, 15, 27, 31}
def rootOne : Mask := 13
def rootTwo : Mask := 14
def fullFamily : Finset Mask := coreFamily ∪ {rootOne, rootTwo}
def tightCoordinates : Finset Ground := {4, 0, 1}

def exactMaskFamily : Finset (Finset Ground) :=
  fullFamily.image maskSet

def exactCoreMaskFamily : Finset (Finset Ground) :=
  coreFamily.image maskSet

def rootOneSet : Finset Ground := maskSet rootOne
def rootTwoSet : Finset Ground := maskSet rootTwo

def claim42254UnionClosure : Prop :=
  exactMaskFamily.card = 7 ∧
    unionClosed (coreFamily.image maskSet) ∧
    unionClosed (coreFamily.image maskSet ∪ {rootOneSet}) ∧
    unionClosed (coreFamily.image maskSet ∪ {rootTwoSet}) ∧
    unionClosed exactMaskFamily

/-- Claim 42254: deleting either or both displayed roots from the exact
seven-member mask family leaves the ordinary union-closed core. -/
def unionClosureBeforeAndAfterRootDeletions_claim42254 : Prop :=
  claim42254UnionClosure

/-- Claim 42255: the three tight coordinates have singleton traces on the two
roots and their retained union is the core mask 15. -/
def singletonTightTracesAndRetainedRootJoin_claim42255 : Prop :=
  rootOneSet ∩ tightCoordinates = {0} ∧
    rootTwoSet ∩ tightCoordinates = {1} ∧
    rootOneSet ∪ rootTwoSet = maskSet 15 ∧
    maskSet 15 ∈ exactCoreMaskFamily

/-- Claim 42256: both displayed pairs collide under both root closures, with
opposite membership of the p₀=4 coordinate. -/
def simultaneousRootClosureCollisionPairs_claim42256 : Prop :=
  (maskSet 7 ∪ rootOneSet = maskSet 15) ∧
    (maskSet 15 ∪ rootOneSet = maskSet 15) ∧
    (maskSet 7 ∪ rootTwoSet = maskSet 15) ∧
    (maskSet 15 ∪ rootTwoSet = maskSet 15) ∧
    (maskSet 27 ∪ rootOneSet = maskSet 31) ∧
    (maskSet 31 ∪ rootOneSet = maskSet 31) ∧
    (maskSet 27 ∪ rootTwoSet = maskSet 31) ∧
    (maskSet 31 ∪ rootTwoSet = maskSet 31) ∧
    (4 : Ground) ∉ maskSet 7 ∧
    (4 : Ground) ∉ maskSet 15 ∧
    (4 : Ground) ∈ maskSet 27 ∧
    (4 : Ground) ∈ maskSet 31

/-- Claim 42257: the complete displayed family has no nonempty singleton or
pair member and contains no member outside the core plus its two roots. -/
def noSmallSetOrEarlierSupportWitness_claim42257 : Prop :=
  (∀ M : Mask, M ∈ fullFamily →
    (maskSet M).Nonempty → 3 ≤ (maskSet M).card) ∧
    fullFamily \ (coreFamily ∪ {rootOne, rootTwo}) = ∅

end MathlibPlus.Open.Combinatorics.R2665BooleanMasks
