import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim22644SharpPositivityThresholds

noncomputable section

private abbrev Three := Fin 3

private def previous (i : Three) : Three :=
  Fin.ofNat 3 (i.1 + 2)

private def next (i : Three) : Three :=
  Fin.ofNat 3 (i.1 + 1)

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

private def sixCodeData {α : Type*} [DecidableEq α]
    (A Q : Three → Finset α)
    (P L : (i : Three) → Finset (Finset α)) : Prop :=
  (∀ i : Three, goodCode (A i) (P i) ∧ goodCode (Q i) (L i)) ∧
    pairwiseDisjointBlocks A Q

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

private def sharpThresholds {α : Type*} [DecidableEq α]
    (A Q : Three → Finset α)
    (P L : (i : Three) → Finset (Finset α)) : Prop :=
  (∀ i : Three, ∀ x ∈ A i,
    -1 ≤ codeDeficit (P i) x) ∧
  (∀ i : Three, ∀ x ∈ Q i,
    0 ≤ codeDeficit (L i) x)

/-- Claim 22644: in the exact six-code Cartesian saturated grid, positivity of
all outside deficits is equivalent to the two sharp coordinate thresholds, and
the four boundary signed-channel values are the displayed ones. -/
def claim22644 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (A Q : Three → Finset α)
    (P L : (i : Three) → Finset (Finset α)),
    sixCodeData A Q P L →
      (allOutsideDeficitsPositive A Q P L ↔
        sharpThresholds A Q P L) ∧
      (∀ i : Three, ∀ x ∈ A i,
        codeDeficit (P i) x = -1 →
          predecessorSignedWeight P L i x = 1) ∧
      (∀ i : Three, ∀ x ∈ A i,
        codeDeficit (P i) x ≤ -2 →
          predecessorSignedWeight P L i x ≤
            -((L (previous i)).card : ℤ)) ∧
      (∀ i : Three, ∀ x ∈ Q i,
        codeDeficit (L i) x = 0 →
          optionalSignedWeight P L i x = (P (next i)).card) ∧
      (∀ i : Three, ∀ x ∈ Q i,
        codeDeficit (L i) x = -1 →
          optionalSignedWeight P L i x = -1)

end

end MathlibPlus.Open.ResearchFormalization.Claim22644SharpPositivityThresholds
