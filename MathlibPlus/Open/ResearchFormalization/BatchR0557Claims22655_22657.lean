import Mathlib
import MathlibPlus.Combinatorics.Claim22656

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR0557Claims22655_22657

private abbrev Three := Fin 3

private def previous (i : Three) : Three :=
  ⟨(i.1 + 2) % 3, by omega⟩

private def next (i : Three) : Three :=
  ⟨(i.1 + 1) % 3, by omega⟩

private def nextTwo (i : Three) : Three :=
  next (next i)

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
    (A Q : Three → Finset α) : Prop :=
  ∀ i j : Three, i ≠ j →
    Disjoint (A i) (A j) ∧
      Disjoint (Q i) (Q j) ∧
      Disjoint (A i) (Q j) ∧
      Disjoint (Q i) (A j) ∧
      Disjoint (A i) (Q i)

private def codedRepairData {α : Type*} [DecidableEq α]
    (A Q : Three → Finset α)
    (P L : (i : Three) → Finset (Finset α)) : Prop :=
  (∀ i : Three, goodCode (A i) (P i) ∧ goodCode (Q i) (L i)) ∧
    pairwiseDisjointBlocks A Q ∧
    (∀ (i : Three) (x : α), x ∈ A i →
      -1 ≤ codeDeficit (P i) x)

private def channelWeight {α : Type*} [DecidableEq α]
    (P L : (i : Three) → Finset (Finset α)) (i : Three) : ℤ :=
  ((((P i).card + 1) * ((L (previous i)).card + 1) + 1 : ℕ) : ℤ)

private def predecessorSignedWeight {α : Type*} [DecidableEq α]
    (P L : (i : Three) → Finset (Finset α)) (i : Three) (x : α) : ℤ :=
  ((L (previous i)).card : ℤ) + 2 +
    (((L (previous i)).card : ℤ) + 1) * codeDeficit (P i) x

private def optionalSignedWeight {α : Type*} [DecidableEq α]
    (P L : (i : Three) → Finset (Finset α)) (i : Three) (x : α) : ℤ :=
  ((P (next i)).card : ℤ) +
    (((P (next i)).card : ℤ) + 1) * codeDeficit (L i) x

private def predecessorGlobalDeficit {α : Type*} [DecidableEq α]
    (P L : (i : Three) → Finset (Finset α)) (i : Three) (x : α) : ℤ :=
  predecessorSignedWeight P L i x *
      channelWeight P L (next i) * channelWeight P L (nextTwo i) - 1

private def optionalGlobalDeficit {α : Type*} [DecidableEq α]
    (P L : (i : Three) → Finset (Finset α)) (i : Three) (x : α) : ℤ :=
  optionalSignedWeight P L i x *
      channelWeight P L (nextTwo i) * channelWeight P L i - 1

private def allOutsideDeficitsPositive {α : Type*} [DecidableEq α]
    (A Q : Three → Finset α)
    (P L : (i : Three) → Finset (Finset α)) : Prop :=
  (∀ i : Three, ∀ x ∈ A i,
    0 < predecessorGlobalDeficit P L i x) ∧
  (∀ i : Three, ∀ x ∈ Q i,
    0 < optionalGlobalDeficit P L i x)

private def optionalCodesHaveNoAbundantCoordinate
    {α : Type*} [DecidableEq α]
    (Q : Three → Finset α)
    (L : (i : Three) → Finset (Finset α)) : Prop :=
  ∀ i : Three, ∀ x ∈ Q i, 0 ≤ codeDeficit (L i) x

private def strictCodeCounterexample {α : Type*} [DecidableEq α]
    (block : Finset α) (L : Finset (Finset α)) : Prop :=
  goodCode block L ∧
    MathlibPlus.Combinatorics.Claim22656.hasNonemptyMember L ∧
    ¬ ∃ x : α,
      2 * MathlibPlus.Combinatorics.Claim22656.supportCount L x > L.card

/-- Claim 22655: after the fixed predecessor-code threshold in the exact
six-code repair, positivity of every outside deficit is equivalent to
non-abundance of every coordinate in every optional code. -/
def claim22655_positiveDeficitsIffOptionalNoAbundance : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (A Q : Three → Finset α)
    (P L : (i : Three) → Finset (Finset α)),
    codedRepairData A Q P L →
      (allOutsideDeficitsPositive A Q P L ↔
        optionalCodesHaveNoAbundantCoordinate Q L)

/-- Claim 22657: in the same exact coded-factor repair, making all outside
 deficits positive is exactly the choice of every optional code as a strict
 no-empty-set Frankl counterexample. -/
def claim22657_positiveDeficitRepairIsFranklComplete : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (A Q : Three → Finset α)
    (P L : (i : Three) → Finset (Finset α)),
    codedRepairData A Q P L →
      (allOutsideDeficitsPositive A Q P L ↔
        ∀ i : Three, strictCodeCounterexample (Q i) (L i))

end MathlibPlus.Open.ResearchFormalization.BatchR0557Claims22655_22657
