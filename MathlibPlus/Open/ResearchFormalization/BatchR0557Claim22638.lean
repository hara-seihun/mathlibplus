import Mathlib

open scoped BigOperators
open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

namespace MathlibPlus.Open.ResearchFormalization.BatchR0557Claim22638

noncomputable section

private abbrev Three := Fin 3

private def previous (i : Three) : Three :=
  Fin.ofNat 3 (i.1 + 2)

private def next (i : Three) : Three :=
  Fin.ofNat 3 (i.1 + 1)

private def nextTwo (i : Three) : Three :=
  next (next i)

private def unionClosed {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ ⦃A B : Finset α⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

private def unionOf {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) : Finset α :=
  H.biUnion (fun S => S)

private def codeOnBlock {α : Type*} [DecidableEq α]
    (block : Finset α) (C : Finset (Finset α)) : Prop :=
  C.Nonempty ∧
    (∅ : Finset α) ∉ C ∧
    (∀ S ∈ C, S.Nonempty ∧ S ⊆ block) ∧
    (∀ S ∈ C, ∀ T ∈ C, S ∪ T ∈ C) ∧
    block ∈ C

private def pairwiseDisjointBlocks {α : Type*} [DecidableEq α]
    (A C : Three → Finset α) : Prop :=
  (∀ i : Three, Disjoint (A i) (C i)) ∧
    (∀ i j : Three, i ≠ j →
      Disjoint (A i) (A j) ∧
        Disjoint (C i) (C j) ∧
        Disjoint (A i) (C j) ∧
        Disjoint (C i) (A j))

private def sixCodeData {α : Type*} [DecidableEq α]
    (t : Three → α) (A C : Three → Finset α)
    (P L : (i : Three) → Finset (Finset α)) : Prop :=
  (∀ i : Three,
    (A i).Nonempty ∧ (C i).Nonempty ∧
      codeOnBlock (A i) (P i) ∧ codeOnBlock (C i) (L i)) ∧
    pairwiseDisjointBlocks A C ∧
    Function.Injective t ∧
    (∀ i : Three, ∀ j : Three, t j ∉ A i ∧ t j ∉ C i)

private def sixCodeGenerators {α : Type*} [DecidableEq α]
    (t : Three → α) (A C : Three → Finset α)
    (P L : (i : Three) → Finset (Finset α)) : Finset (Finset α) :=
  (Finset.univ : Finset Three).biUnion (fun i =>
    (P i).image (fun S => insert (t i) S) ∪
      {C i} ∪
      (L i).image (fun S => insert (t (next i)) S))

private def sixCodeFamily {α : Type*} [Fintype α] [DecidableEq α]
    (t : Three → α) (A C : Three → Finset α)
    (P L : (i : Three) → Finset (Finset α)) : Finset (Finset α) :=
  ((sixCodeGenerators t A C P L).powerset.image unionOf).erase ∅

private def tightSet {α : Type*} [DecidableEq α]
    (t : Three → α) : Finset α :=
  (Finset.univ : Finset Three).image t

private def traceCell {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (T B : Finset α) : Finset (Finset α) :=
  T.powerset.filter (fun S => S ∪ B ∈ F)

private def predecessorBlock {α : Type*} [DecidableEq α]
    (C : Three → Finset α) (p : Three → Finset α) (i : Three) : Finset α :=
  p i ∪ C i

private def cartesianTarget {α : Type*} [DecidableEq α]
    (C : Three → Finset α) (p : Three → Finset α) : Finset α :=
  unionOf ((Finset.univ : Finset Three).image (predecessorBlock C p))

private def cartesianDescendant {α : Type*} [DecidableEq α]
    (C : Three → Finset α) (p : Three → Finset α) (i : Three) : Finset α :=
  C i ∪ predecessorBlock C p (next i) ∪
    predecessorBlock C p (nextTwo i)

private def validPredecessors {α : Type*} [DecidableEq α]
    (P : Three → Finset (Finset α)) (p : Three → Finset α) : Prop :=
  ∀ i : Three, p i ∈ P i

private def completeBlockerSet {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (T U : Finset α) (i : Three)
    (t : Three → α) : Finset α :=
  U \ ((U.powerset.filter (fun B =>
    (traceCell F T B ∩ (T.erase (t i)).powerset).Nonempty)).biUnion
      (fun B => B))

private def sourceTraceA {α : Type*} [DecidableEq α]
    (t : Three → α) (i : Three) : Finset (Finset α) :=
  {({t i} : Finset α)}

private def sourceTraceC {α : Type*} [DecidableEq α]
    (t : Three → α) (i : Three) : Finset (Finset α) :=
  {∅, {t (next i)}}

private def sourceTraceB {α : Type*} [DecidableEq α]
    (t : Three → α) (i : Three) : Finset (Finset α) :=
  {{t i}, {t i, t (next i)}}

private def topTrace {α : Type*} [DecidableEq α]
    (t : Three → α) : Finset (Finset α) :=
  {tightSet t}

private def coatomTrace {α : Type*} [DecidableEq α]
    (t : Three → α) (i : Three) : Finset (Finset α) :=
  {tightSet t \ {t i}, tightSet t}

private def exactFanCertificates {α : Type*} [Fintype α] [DecidableEq α]
    (t : Three → α) (A C : Three → Finset α)
    (P L : (i : Three) → Finset (Finset α)) : Prop :=
  let F := sixCodeFamily t A C P L
  let T := tightSet t
  (∀ i : Three,
    traceCell F T (A i) = sourceTraceA t i ∧
      traceCell F T (C i) = sourceTraceC t i) ∧
    (∀ p : Three → Finset α,
      validPredecessors P p →
        (∀ i : Three,
          traceCell F T (predecessorBlock C p i) = sourceTraceB t i) ∧
        traceCell F T (cartesianTarget C p) = topTrace t ∧
        (∀ i : Three,
          traceCell F T (cartesianDescendant C p i) = coatomTrace t i ∧
          cartesianTarget C p \ cartesianDescendant C p i = p i ∧
          p i ⊆ completeBlockerSet F T (cartesianTarget C p) i t))

private def ordinarySixCodeSymmetricExtension
    {α : Type*} [Fintype α] [DecidableEq α]
    (t : Three → α) (A C : Three → Finset α)
    (P L : (i : Three) → Finset (Finset α)) : Prop :=
  let F := sixCodeFamily t A C P L
  F.Nonempty ∧
    ∅ ∉ F ∧
    unionClosed F ∧
    exactFanCertificates t A C P L

/-- The union closure of the six exact code families is the ordinary
empty-free cyclic saturated-grid extension, with its source, top, coatom,
gap, and complete blocker carriers written explicitly. -/
def claim22638 : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (t : Three → α) (A C : Three → Finset α)
    (P L : (i : Three) → Finset (Finset α)),
    sixCodeData t A C P L →
      ordinarySixCodeSymmetricExtension t A C P L

end

end MathlibPlus.Open.ResearchFormalization.BatchR0557Claim22638
