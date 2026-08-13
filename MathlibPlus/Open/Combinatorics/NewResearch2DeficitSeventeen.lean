import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Cayley

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics
noncomputable section
open Classical

structure FiniteUnionSemilattice (α : Type*) [DecidableEq α] where
  members : Finset (Finset α)
  nonempty : members.Nonempty
  union_mem : ∀ ⦃A B : Finset α⦄, A ∈ members → B ∈ members → A ∪ B ∈ members

def signature {α : Type*} [DecidableEq α] (L : FiniteUnionSemilattice α) (s : Finset α) : Finset (Finset α) :=
  L.members.filter (fun r => ¬ s ⊆ r)
def signatureFamily {α : Type*} [DecidableEq α] (L : FiniteUnionSemilattice α) : Finset (Finset (Finset α)) :=
  L.members.image (signature L)
def signatureInjective {α : Type*} [DecidableEq α] (L : FiniteUnionSemilattice α) : Prop :=
  ∀ ⦃s t : Finset α⦄, s ∈ L.members → t ∈ L.members → signature L s = signature L t → s = t
def signatureUnionClosed {α : Type*} [DecidableEq α] (L : FiniteUnionSemilattice α) : Prop :=
  ∀ ⦃A B : Finset (Finset α)⦄, A ∈ signatureFamily L → B ∈ signatureFamily L → A ∪ B ∈ signatureFamily L
def signatureGround {α : Type*} [DecidableEq α] (L : FiniteUnionSemilattice α) : Finset (Finset α) :=
  (signatureFamily L).biUnion (fun s => s)
def signatureFrequency {α : Type*} [DecidableEq α] (L : FiniteUnionSemilattice α) (h : Finset α) : ℕ :=
  ((signatureFamily L).filter (fun s => h ∈ s)).card
def majoritySignature {α : Type*} [DecidableEq α] (L : FiniteUnionSemilattice α) : Prop :=
  signatureUnionClosed L ∧ ∀ h ∈ signatureGround L, 2 * signatureFrequency L h < (signatureFamily L).card
def signatureJoinEmbedding {α : Type*} [DecidableEq α] (L : FiniteUnionSemilattice α) : Prop :=
  signatureInjective L ∧ ∀ ⦃s t : Finset α⦄, s ∈ L.members → t ∈ L.members → signature L (s ∪ t) = signature L s ∪ signature L t
def unionIrreducibleMember {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (T : Finset α) : Prop :=
  T ∈ F ∧ T.Nonempty ∧ ∀ ⦃A B : Finset α⦄, A ∈ F → B ∈ F → A ∪ B = T → A = T ∨ B = T
def removableUnionMember {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (T : Finset α) : Prop :=
  T ∈ F ∧ ∀ ⦃A B : Finset α⦄, A ∈ F.erase T → B ∈ F.erase T → A ∪ B ∈ F.erase T
def joinIrreducibleMember {α : Type*} [DecidableEq α] (L : FiniteUnionSemilattice α) (j : Finset α) : Prop :=
  j ∈ L.members ∧ j.Nonempty ∧ ∀ ⦃A B : Finset α⦄, A ∈ L.members → B ∈ L.members → A ∪ B = j → A = j ∨ B = j
def injectiveSignatureTransportsJoinIrreducibility_claim26654 : Prop :=
  ∀ {α : Type*} [DecidableEq α] (L : FiniteUnionSemilattice α), majoritySignature L → signatureInjective L →
    signatureJoinEmbedding L ∧ ∀ ⦃j : Finset α⦄, joinIrreducibleMember L j →
      (signature L j).Nonempty ∧ unionIrreducibleMember (signatureFamily L) (signature L j) ∧ removableUnionMember (signatureFamily L) (signature L j) ∧
      ∀ ⦃h : Finset α⦄, h ∈ L.members → ¬ j ⊆ h → h ∈ signature L j

def familyGround {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Finset α := F.biUnion (fun A => A)
def familyFrequency {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α) : ℕ := (F.filter (fun A => x ∈ A)).card
def unionClosedFamily {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop := ∀ ⦃A B : Finset α⦄, A ∈ F → B ∈ F → A ∪ B ∈ F
def franklCounterexample {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop := F.Nonempty ∧ unionClosedFamily F ∧ ∀ x ∈ familyGround F, 2 * familyFrequency F x < F.card
def globallyMinimumFranklCounterexample {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop := franklCounterexample F ∧ ∀ (G : Finset (Finset α)), franklCounterexample G → F.card ≤ G.card
def normalizedCounterexample {α : Type*} [DecidableEq α] (F N : Finset (Finset α)) : Prop := franklCounterexample N ∧ N.card = F.card ∧ ∀ x : α, familyFrequency N x ≤ familyFrequency F x
def tightCoordinate {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α) : Prop := x ∈ familyGround F ∧ 2 * familyFrequency F x + 1 = F.card
def tightCoordinateCount {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : ℕ := (familyGround F).filter (fun x => decide (tightCoordinate F x)) |>.card
def franklMinimum53TightInterface_claim26656 : Prop :=
  (∀ {α : Type*} [DecidableEq α] (F : Finset (Finset α)), franklCounterexample F → F.card = 53 → globallyMinimumFranklCounterexample F) ∧
  (∀ {α : Type*} [DecidableEq α] (F : Finset (Finset α)), globallyMinimumFranklCounterexample F → F.card = 53 → (∃ N : Finset (Finset α), normalizedCounterexample F N) ∧ ∀ N : Finset (Finset α), normalizedCounterexample F N → 3 ≤ tightCoordinateCount N) ∧
  ¬ ∃ (α : Type*) (_ : DecidableEq α) (F : Finset (Finset α)), globallyMinimumFranklCounterexample F ∧ F.card = 53 ∧ tightCoordinateCount F ≤ 1

structure DeficitSeventeenProfile (ι : Type*) [DecidableEq ι] where
  k : ℕ
  deficit : ℕ
  semilattice : FiniteUnionSemilattice ι
  singletonRoots : Finset (Finset ι)
  neutralRoots : Finset (Finset ι)
  lowerFull : Finset ι
  rootLabel : Finset ι → Fin 3
def profileSignature {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) : Finset (Finset (Finset ι)) := signatureFamily P.semilattice
def profileFrequency {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) (h : Finset ι) : ℕ := ((profileSignature P).filter (fun q => h ∈ q)).card
def positiveNeutralDeficitSeventeen {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) : Prop := P.deficit = 17 ∧ P.singletonRoots.Nonempty ∧ P.neutralRoots.Nonempty ∧ Disjoint P.singletonRoots P.neutralRoots ∧ P.lowerFull ∉ P.singletonRoots ∧ P.lowerFull ∉ P.neutralRoots ∧ P.semilattice.members.Nonempty ∧ P.singletonRoots ⊆ P.semilattice.members ∧ P.neutralRoots ⊆ P.semilattice.members ∧ P.lowerFull ∈ P.semilattice.members
def profileAdmissible {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) : Prop := positiveNeutralDeficitSeventeen P ∧ signatureUnionClosed P.semilattice ∧ (profileSignature P).card = P.k + 9 ∧ majoritySignature P.semilattice
def profileSignatureInjective {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) : Prop := signatureInjective P.semilattice
def profileJoinIrreducible {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) (q : Finset (Finset ι)) : Prop := unionIrreducibleMember (profileSignature P) q
def profileOutsideJoinIrreducible {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) (q : Finset (Finset ι)) : Prop := profileJoinIrreducible P q ∧ P.lowerFull ∈ q
def profileEmptyDeleted {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) (q : Finset (Finset ι)) : Finset (Finset (Finset ι)) := ((profileSignature P).erase (∅ : Finset (Finset ι))).erase q
def profileTwoDeleted {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) (q₁ q₂ : Finset (Finset ι)) : Finset (Finset (Finset ι)) := (((profileSignature P).erase (∅ : Finset (Finset ι))).erase q₁).erase q₂
def profileFourDeleted {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) (q₁ q₂ q₃ q₄ : Finset (Finset ι)) : Finset (Finset (Finset ι)) := ((((profileSignature P).erase (∅ : Finset (Finset ι))).erase q₁).erase q₂).erase q₃ |>.erase q₄
def profileEndpointCounterexample {ι : Type*} [DecidableEq ι] (Q : Finset (Finset (Finset ι))) : Prop := franklCounterexample Q ∧ Q.card = 53 ∧ tightCoordinateCount Q ≤ 1
def sixDistinctJoinIrreducibles {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) : Prop := ∃ q₁ q₂ q₃ q₄ q₅ q₆ : Finset (Finset ι), [q₁, q₂, q₃, q₄, q₅, q₆].Pairwise (· ≠ ·) ∧ profileJoinIrreducible P q₁ ∧ profileJoinIrreducible P q₂ ∧ profileJoinIrreducible P q₃ ∧ profileJoinIrreducible P q₄ ∧ profileJoinIrreducible P q₅ ∧ profileJoinIrreducible P q₆
def fourDistinctJoinIrreducibles {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) : Prop := ∃ q₁ q₂ q₃ q₄ : Finset (Finset ι), [q₁, q₂, q₃, q₄].Pairwise (· ≠ ·) ∧ profileJoinIrreducible P q₁ ∧ profileJoinIrreducible P q₂ ∧ profileJoinIrreducible P q₃ ∧ profileJoinIrreducible P q₄
def profileIdealBelowLowerFull {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) : Finset (Finset (Finset ι)) := (profileSignature P).filter (fun q => P.lowerFull ∉ q)
def deficitSeventeenK46Exclusion_claim26657 : Prop := (¬ ∃ (ι : Type*) (_ : DecidableEq ι) (P : DeficitSeventeenProfile ι), profileAdmissible P ∧ P.k = 46 ∧ profileSignatureInjective P) ∧ ∀ {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι), profileAdmissible P → P.k = 46 → profileSignatureInjective P → (profileSignature P).card = 55 ∧ (∅ : Finset (Finset ι)) ∈ profileSignature P ∧ (∀ h ∈ P.singletonRoots, profileFrequency P h ≤ 23) ∧ (∀ h ∈ P.neutralRoots, profileFrequency P h ≤ 22) ∧ profileFrequency P P.lowerFull ≤ 27 ∧ ∃ q : Finset (Finset ι), profileOutsideJoinIrreducible P q ∧ profileEndpointCounterexample (profileEmptyDeleted P q)
def deficitSeventeenK47Exclusion_claim26658 : Prop := (¬ ∃ (ι : Type*) (_ : DecidableEq ι) (P : DeficitSeventeenProfile ι), profileAdmissible P ∧ P.k = 47 ∧ profileSignatureInjective P) ∧ ∀ {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι), profileAdmissible P → P.k = 47 → profileSignatureInjective P → (profileSignature P).card = 56 ∧ (∀ h ∈ P.singletonRoots, profileFrequency P h ≤ 24) ∧ (∀ h ∈ P.neutralRoots, profileFrequency P h ≤ 23) ∧ profileFrequency P P.lowerFull ≤ 27 ∧ sixDistinctJoinIrreducibles P ∧ ∃ q₁ q₂ : Finset (Finset ι), profileOutsideJoinIrreducible P q₁ ∧ profileJoinIrreducible P q₂ ∧ q₁ ≠ q₂ ∧ profileEndpointCounterexample (profileTwoDeleted P q₁ q₂)
def deficitSeventeenK49Exclusion_claim26660 : Prop := (¬ ∃ (ι : Type*) (_ : DecidableEq ι) (P : DeficitSeventeenProfile ι), profileAdmissible P ∧ P.k = 49 ∧ profileSignatureInjective P) ∧ ∀ {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι), profileAdmissible P → P.k = 49 → profileSignatureInjective P → (profileSignature P).card = 58 ∧ (∀ h ∈ P.singletonRoots, profileFrequency P h ≤ 25) ∧ (∀ h ∈ P.neutralRoots, profileFrequency P h ≤ 24) ∧ profileFrequency P P.lowerFull ≤ 28 ∧ ((profileFrequency P P.lowerFull ≤ 26) ∨ (profileFrequency P P.lowerFull = 27 ∧ ∃ q : Finset (Finset ι), profileOutsideJoinIrreducible P q) ∨ (profileFrequency P P.lowerFull = 28 ∧ (profileIdealBelowLowerFull P).card = 30 ∧ ((profileSignature P).filter (fun q => P.lowerFull ∈ q)).card = 28 ∧ ∃ q₁ q₂ : Finset (Finset ι), profileOutsideJoinIrreducible P q₁ ∧ profileOutsideJoinIrreducible P q₂ ∧ q₁ ≠ q₂)) ∧ sixDistinctJoinIrreducibles P ∧ fourDistinctJoinIrreducibles P ∧ ∃ q₁ q₂ q₃ q₄ : Finset (Finset ι), [q₁, q₂, q₃, q₄].Pairwise (· ≠ ·) ∧ profileEndpointCounterexample (profileFourDeleted P q₁ q₂ q₃ q₄)
def deficitSeventeenThroughK50Exclusion_claim26691 : Prop := ∀ {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι), profileAdmissible P → profileSignatureInjective P → 17 ≤ P.k → P.k ≤ 50 → False
def coordinateMinimalMember {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α) (A : Finset α) : Prop := A ∈ F ∧ x ∈ A ∧ ∀ ⦃B : Finset α⦄, B ∈ F → x ∈ B → A ⊆ B
def inclusionMinimalNonemptyMember {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (A : Finset α) : Prop := A ∈ F ∧ A.Nonempty ∧ ∀ ⦃B : Finset α⦄, B ∈ F → B ⊆ A → B.Nonempty → B = A
def k50Deleted {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) (q₁ q₂ q₃ p₁ p₂ : Finset (Finset ι)) : Finset (Finset (Finset ι)) := (((((profileSignature P).erase q₁).erase q₂).erase q₃).erase p₁).erase p₂ |>.erase ∅
def deficitSeventeenK50Endpoint_claim26692 : Prop := ∀ {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι), profileAdmissible P → P.k = 50 → profileSignatureInjective P → (profileSignature P).card = 59 ∧ profileFrequency P P.lowerFull ≤ 29 ∧ (∀ h ∈ P.singletonRoots, profileFrequency P h ≤ 25) ∧ (∀ h ∈ P.neutralRoots, profileFrequency P h ≤ 24) ∧ ∃ q₁ q₂ q₃ p₁ p₂ : Finset (Finset ι), coordinateMinimalMember (profileSignature P) P.lowerFull q₁ ∧ coordinateMinimalMember ((profileSignature P).erase q₁) P.lowerFull q₂ ∧ coordinateMinimalMember (((profileSignature P).erase q₁).erase q₂) P.lowerFull q₃ ∧ inclusionMinimalNonemptyMember ((((profileSignature P).erase q₁).erase q₂).erase q₃) p₁ ∧ inclusionMinimalNonemptyMember (((((profileSignature P).erase q₁).erase q₂).erase q₃).erase p₁) p₂ ∧ profileEndpointCounterexample (((((profileSignature P).erase q₁).erase q₂).erase q₃).erase p₁ |>.erase p₂ |>.erase ∅)
def complementSupports {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) (r : Finset ι) : Finset (Finset ι) := P.semilattice.members.filter (fun q => ¬ q ⊆ r)
def profilePartitionedComplement {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι) (r : Finset ι) (Q P₀ N : Finset (Finset ι)) : Prop := Q ⊆ complementSupports P r ∧ P₀ ⊆ complementSupports P r ∧ N ⊆ complementSupports P r ∧ (∀ q ∈ N, q ∈ P.neutralRoots) ∧ Disjoint Q P₀ ∧ Disjoint Q N ∧ Disjoint P₀ N ∧ Q ∪ P₀ ∪ N = complementSupports P r ∧ Q.card = 2 ∧ P₀.card = 4 ∧ N.card = 20 ∧ (∑ q ∈ Q, q.card) = 16 ∧ (∑ q ∈ P₀, q.card) = 12 ∧ (∀ q ∈ N, 2 ≤ q.card)
def deficitSeventeenK51EqualityRigidity_claim26693 : Prop := ∀ {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι), profileAdmissible P → P.k = 51 → profileSignatureInjective P → ∀ r ∈ P.singletonRoots, profileFrequency P r = 26 → (profileSignature P).card = 60 ∧ (∃ Q P₀ N : Finset (Finset ι), profilePartitionedComplement P r Q P₀ N) ∧ (∑ q ∈ complementSupports P r, q.card) = 68 ∧ (∑ q ∈ complementSupports P r, q.card) ≤ P.k + 17 ∧ ∃ s t : Finset ι, s ∈ P.semilattice.members ∧ t ∈ P.semilattice.members ∧ s ≠ t ∧ s.card = 1 ∧ t.card = 1 ∧ P.rootLabel s = P.rootLabel r ∧ P.rootLabel t = P.rootLabel r ∧ s ⊆ r ∧ t ⊆ r
def deficitSeventeenThroughK51Exclusion_claim26696 : Prop := ∀ {ι : Type*} [DecidableEq ι] (P : DeficitSeventeenProfile ι), profileAdmissible P → profileSignatureInjective P → 17 ≤ P.k → P.k ≤ 51 → False
def familyAfter {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (xs : List (Finset α)) (i : ℕ) : Finset (Finset α) := (xs.take i).foldl (fun M A => M.erase A) F
def validTargetedDeletionSequence {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α) (xs : List (Finset α)) : Prop := xs.Nodup ∧ (∀ (i : ℕ) (hi : i < xs.length), let A := xs.get ⟨i, hi⟩; A ∈ familyAfter F xs i ∧ x ∈ A ∧ coordinateMinimalMember (familyAfter F xs i) x A ∧ unionClosedFamily ((familyAfter F xs i).erase A)) ∧ (∀ i ≤ xs.length, unionClosedFamily (familyAfter F xs i))
def arbitrarySequentialTargetedDeletion_claim26689 : Prop := ∀ {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α) (r : ℕ), unionClosedFamily F → r ≤ familyFrequency F x → ∃ xs : List (Finset α), xs.length = r ∧ validTargetedDeletionSequence F x xs ∧ familyFrequency (familyAfter F xs xs.length) x = familyFrequency F x - r
end
end MathlibPlus.Open.Combinatorics

