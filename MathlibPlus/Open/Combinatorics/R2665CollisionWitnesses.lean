import Mathlib
import MathlibPlus.Combinatorics.BooleanComponentSeparation

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Combinatorics.R2665CollisionWitnesses

abbrev Ground := Fin 5
abbrev Mask := ℕ

/-- The subset of the five-coordinate ground represented by a bit mask. -/
def maskSet (m : Mask) : Finset Ground :=
  Finset.univ.filter (fun i => Nat.testBit m i.val = true)

/-- Ordinary union closure for a finite family of ground subsets. -/
def unionClosed (F : Finset (Finset Ground)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

def coreFamily : Finset Mask := {0, 7, 15, 27, 31}
def rootOne : Mask := 13
def rootTwo : Mask := 14
def fullFamily : Finset Mask := coreFamily ∪ {rootOne, rootTwo}
def tightCoordinates : Finset Ground := {4, 0, 1}
def exactFamily : Finset (Finset Ground) := fullFamily.image maskSet
def exactCoreFamily : Finset (Finset Ground) := coreFamily.image maskSet
def rootOneSet : Finset Ground := maskSet rootOne
def rootTwoSet : Finset Ground := maskSet rootTwo

def explicitFamilyData : Prop :=
  let p₀ : Fin 5 := 4
  let p₁ : Fin 5 := 0
  let p₂ : Fin 5 := 1
  let G : Finset ℕ := {0, 7, 15, 27, 31}
  let R₁ : ℕ := 13
  let R₂ : ℕ := 14
  let F := G ∪ {R₁, R₂}
  p₀ = 4 ∧ p₁ = 0 ∧ p₂ = 1 ∧
    (∀ m ∈ F, m < 2 ^ 5) ∧ F.card = 7

/-- Deleting either or both roots is the endpoint-extension meaning of
removability used by the retained countermodel. -/
def removableRootExtension : Prop :=
  unionClosed exactCoreFamily ∧
    unionClosed (exactCoreFamily ∪ {rootOneSet}) ∧
    unionClosed (exactCoreFamily ∪ {rootTwoSet}) ∧
    unionClosed exactFamily

def singletonTraceAndJoin : Prop :=
  rootOneSet ∩ tightCoordinates = {0} ∧
    rootTwoSet ∩ tightCoordinates = {1} ∧
    rootOneSet ∪ rootTwoSet = maskSet 15 ∧
    maskSet 15 ∈ exactCoreFamily

def collisionPair (q : Fin 2) : Finset Ground × Finset Ground :=
  if q = 0 then (maskSet 7, maskSet 15) else (maskSet 27, maskSet 31)

def rootMask (i : Fin 2) : Finset Ground :=
  if i = 0 then rootOneSet else rootTwoSet

def rootClosureCollision : Prop :=
  ∀ (q i : Fin 2),
    (collisionPair q).1 ∪ rootMask i =
      (collisionPair q).2 ∪ rootMask i

def lowerCollisionPair : Prop :=
  ∀ q : Fin 2, q = 0 →
    (4 : Ground) ∉ (collisionPair q).1 ∧
      (4 : Ground) ∉ (collisionPair q).2

def upperCollisionPair : Prop :=
  ∀ q : Fin 2, q = 1 →
    (4 : Ground) ∈ (collisionPair q).1 ∧
      (4 : Ground) ∈ (collisionPair q).2

def twoDistinctCollisionPairs : Prop :=
  (collisionPair 0).1 ≠ (collisionPair 1).1 ∧
    (collisionPair 0).2 ≠ (collisionPair 1).2

def twoRootCollisionExtension : Prop :=
  singletonTraceAndJoin ∧ removableRootExtension ∧
    twoDistinctCollisionPairs ∧ rootClosureCollision ∧
    lowerCollisionPair ∧ upperCollisionPair

def noSmallMemberOrEarlierSupport : Prop :=
  (∀ M : Mask, M ∈ fullFamily →
    (maskSet M).Nonempty → 3 ≤ (maskSet M).card) ∧
    fullFamily \ (coreFamily ∪ {rootOne, rootTwo}) = ∅

/-- The two collision equations are retained-node equations.  A map of the
 two collision indices into the displayed earlier-support carrier would be
 the missing provenance identification needed to book them historically. -/
def earlierDeletedSupport : Finset Mask :=
  fullFamily \ (coreFamily ∪ {rootOne, rootTwo})

def identifiesEarlierDeletedSupports (φ : Fin 2 → Mask) : Prop :=
  (Function.Injective φ) ∧ ∀ q, φ q ∈ earlierDeletedSupport

def twoAdditionalEarlierSharpCoverIncidences : Prop :=
  ∃ φ : Fin 2 → Mask, identifiesEarlierDeletedSupports φ

def retainedCollisionEquations : Prop :=
  rootClosureCollision ∧ twoDistinctCollisionPairs

def collisionToHistoryImplication : Prop :=
  retainedCollisionEquations → twoAdditionalEarlierSharpCoverIncidences

/-- Claim 42258: the concrete endpoint extension has the two removable
singleton-trace roots, retained join, and two simultaneous collision pairs,
but no additional earlier support.  Thus the collision-to-history charge is
not an implication of the endpoint equations; a provenance map to actual
deleted nodes is an additional datum rather than a consequence of collision. -/
def collisionWitnessesDoNotImplyHistoricalCoverIncidences_claim42258 : Prop :=
  explicitFamilyData ∧
    twoRootCollisionExtension ∧
    noSmallMemberOrEarlierSupport ∧
    retainedCollisionEquations ∧
    ¬ twoAdditionalEarlierSharpCoverIncidences ∧
    ¬ collisionToHistoryImplication

end MathlibPlus.Open.Combinatorics.R2665CollisionWitnesses
