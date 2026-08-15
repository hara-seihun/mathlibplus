import Mathlib

namespace MathlibPlus.Open.FormalizationBatchCompression

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

def familyContainedIn (X : Finset α) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, A ⊆ X

def familyUnion (F : Finset (Finset α)) : Finset α := by
  classical
  exact F.biUnion id

def unionClosedFamily (F : Finset (Finset α)) : Prop :=
  ∀ ⦃A B : Finset α⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

def principalRoot (F : Finset (Finset α)) (x : α) : Finset α := by
  classical
  exact (F.filter (fun A => x ∉ A)).biUnion id

def principalRoots (X : Finset α) (F : Finset (Finset α)) : Finset (Finset α) := by
  classical
  exact X.image (principalRoot F)

def compressedCoordinate (R : Finset (Finset α)) (A : Finset α) : Finset (Finset α) := by
  classical
  exact R.filter (fun r => ¬A ⊆ r)

def inclusionChain (C : Finset (Finset α)) : Prop :=
  ∀ ⦃r s : Finset α⦄, r ∈ C → s ∈ C → r ⊆ s ∨ s ⊆ r

/-- A disjoint union of at most four inclusion chains covering exactly R. -/
def disjointChainCoverAtMostFour (R : Finset (Finset α)) : Prop :=
  ∃ C : Finset (Finset (Finset α)),
    C.card ≤ 4 ∧
    (∀ c ∈ C, inclusionChain c ∧ c ⊆ R) ∧
    (∀ r ∈ R, ∃! c, c ∈ C ∧ r ∈ c)

def franklWitness (X : Finset α) (F : Finset (Finset α)) : Prop :=
  ∃ x ∈ X, F.card ≤ 2 * (F.filter (fun A => x ∈ A)).card

def hasUniversalCoordinate (X : Finset α) (F : Finset (Finset α)) : Prop :=
  ∃ x ∈ X, ∀ A ∈ F, x ∈ A

/-- The four-chain root criterion implies a Frankl witness, including its equivalent
counterexample formulation. -/
def principalRootChainBoundClaim46594 : Prop :=
  ∀ (X : Finset α) (F : Finset (Finset α)),
    familyContainedIn X F →
    unionClosedFamily F →
    familyUnion F = X →
    (hasUniversalCoordinate X F → franklWitness X F) ∧
    ((¬hasUniversalCoordinate X F ∧
        disjointChainCoverAtMostFour (principalRoots X F)) → franklWitness X F) ∧
    (¬franklWitness X F →
      ¬disjointChainCoverAtMostFour (principalRoots X F))

/-- The principal-root compression is injective, preserves unions, and has the same
family cardinality. -/
def principalRootCompressionClaim46603 : Prop :=
  ∀ (X : Finset α) (F : Finset (Finset α)),
    familyContainedIn X F →
    unionClosedFamily F →
    let R := principalRoots X F
    let Φ := compressedCoordinate R
    (∀ ⦃A B : Finset α⦄, A ∈ F → B ∈ F → Φ A = Φ B → A = B) ∧
    (∀ ⦃A B : Finset α⦄, A ∈ F → B ∈ F → Φ (A ∪ B) = Φ A ∪ Φ B) ∧
    (F.image Φ).card = F.card ∧
    unionClosedFamily (F.image Φ)

/-- A root coordinate has exactly the zero members and frequency asserted by the
compression. -/
def principalRootFrequencyClaim46607 : Prop :=
  ∀ (X : Finset α) (F : Finset (Finset α)),
    familyContainedIn X F →
    ∀ x ∈ X,
      let r := principalRoot F x
      let R := principalRoots X F
      let Φ := compressedCoordinate R
      F.filter (fun A => r ∉ Φ A) = F.filter (fun A => A ⊆ r) ∧
      F.filter (fun A => A ⊆ r) = F.filter (fun A => x ∉ A) ∧
      (F.filter (fun A => r ∈ Φ A)).card =
        (F.filter (fun A => x ∈ A)).card

end

end MathlibPlus.Open.FormalizationBatchCompression
