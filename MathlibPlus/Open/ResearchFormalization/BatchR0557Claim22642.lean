import Mathlib

open scoped BigOperators
open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

namespace MathlibPlus.Open.ResearchFormalization.BatchR0557Claim22642

noncomputable section

private abbrev Three := Fin 3

private def previous (i : Three) : Three :=
  Fin.ofNat 3 (i.1 + 2)

private def codeDeficit {α : Type*} [DecidableEq α]
    (C : Finset (Finset α)) (x : α) : ℤ :=
  ((C.filter (fun S => x ∉ S)).card : ℤ) -
    ((C.filter (fun S => x ∈ S)).card : ℤ)

private def goodCode {α : Type*} [DecidableEq α]
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
    (A C : Three → Finset α)
    (P L : (i : Three) → Finset (Finset α)) : Prop :=
  (∀ i : Three, (A i).Nonempty ∧ (C i).Nonempty ∧
    goodCode (A i) (P i) ∧ goodCode (C i) (L i)) ∧
    pairwiseDisjointBlocks A C

private def channelStates {α : Type*} [DecidableEq α]
    (P L : (i : Three) → Finset (Finset α)) (i : Three) :
    Finset (Sum (Finset α × Finset α) Unit) :=
  ((insert ∅ (P i)).product (insert ∅ (L (previous i)))).image
      (fun s : Finset α × Finset α =>
        (Sum.inl s : Sum (Finset α × Finset α) Unit)) ∪
    {Sum.inr ()}

private def channelStateCount {α : Type*} [DecidableEq α]
    (P L : (i : Three) → Finset (Finset α)) (i : Three) : ℕ :=
  (channelStates P L i).card

private def stateSignA {α : Type*} [DecidableEq α]
    (s : Sum (Finset α × Finset α) Unit) (x : α) : ℤ :=
  match s with
  | Sum.inl (S, _) => if x ∈ S then -1 else 1
  | Sum.inr _ => 1

private def stateSignC {α : Type*} [DecidableEq α]
    (s : Sum (Finset α × Finset α) Unit) (x : α) : ℤ :=
  match s with
  | Sum.inl (_, S) => if x ∈ S then -1 else 1
  | Sum.inr _ => -1

private def tightSignedWeight {α : Type*} [DecidableEq α]
    (P L : (i : Three) → Finset (Finset α)) (i : Three) (x : α) : ℤ :=
  ∑ s ∈ channelStates P L i, stateSignA s x

private def optionalSignedWeight {α : Type*} [DecidableEq α]
    (P L : (i : Three) → Finset (Finset α)) (i : Three) (x : α) : ℤ :=
  ∑ s ∈ channelStates P L i, stateSignC s x

/-- The channel is the actual product of the predecessor and optional code
states, with their empty states, plus the distinguished global state. -/
def claim22642 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (A C : Three → Finset α)
    (P L : (i : Three) → Finset (Finset α)),
    sixCodeData A C P L →
      (∀ i : Three,
        channelStateCount P L i =
            ((P i).card + 1) * ((L (previous i)).card + 1) + 1) ∧
      (∀ i : Three, ∀ x ∈ A i,
        tightSignedWeight P L i x =
          ((L (previous i)).card : ℤ) + 2 +
            (((L (previous i)).card : ℤ) + 1) * codeDeficit (P i) x) ∧
      (∀ i : Three, ∀ x ∈ C (previous i),
        optionalSignedWeight P L i x =
          ((P i).card : ℤ) +
            (((P i).card : ℤ) + 1) * codeDeficit (L (previous i)) x)

end

end MathlibPlus.Open.ResearchFormalization.BatchR0557Claim22642
