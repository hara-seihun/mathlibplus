import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim22658CanonicalSeparatingBlocks

noncomputable section

private abbrev Three := Fin 3

private def codeDeficit {α : Type*} [DecidableEq α]
    (C : Finset (Finset α)) (x : α) : ℤ :=
  ((C.filter (fun S => x ∉ S)).card : ℤ) -
    ((C.filter (fun S => x ∈ S)).card : ℤ)

private def canonicalCode {α : Type*} [DecidableEq α]
    (Q : Finset α) : Finset (Finset α) :=
  Q.powerset.erase ∅

private def canonicalBlocks {α : Type*} [DecidableEq α]
    (G : Finset α) (Q : Three → Finset α) (b : ℕ) : Prop :=
  1 ≤ b ∧
    G.Nonempty ∧
    G.card = b ∧
    (∀ i : Three, (Q i).Nonempty ∧ (Q i).card = b) ∧
    (∀ i j : Three, i ≠ j → Disjoint (Q i) (Q j)) ∧
    (∀ i : Three, Disjoint G (Q i))

private def channelWeight {α : Type*} [DecidableEq α]
    (Q : Three → Finset α) (i : Three) : ℤ :=
  ((2 * (canonicalCode (Q i)).card + 3 : ℕ) : ℤ)

private def gChannelWeight {α : Type*} [DecidableEq α]
    (G : Finset α) (Q : Three → Finset α) : ℤ :=
  ((2 ^ G.card * ((canonicalCode (Q 2)).card + 1) + 1 : ℕ) : ℤ)

private def anchorZeroDeficit {α : Type*} [DecidableEq α]
    (G : Finset α) (Q : Three → Finset α) : ℤ :=
  channelWeight Q 1 * gChannelWeight G Q - 1

private def anchorOneDeficit {α : Type*} [DecidableEq α]
    (G : Finset α) (Q : Three → Finset α) : ℤ :=
  channelWeight Q 0 * gChannelWeight G Q - 1

private def deltaG {α : Type*} [DecidableEq α]
    (Q : Three → Finset α) : ℤ :=
  channelWeight Q 0 * channelWeight Q 1 - 1

private def deltaQTwo {α : Type*} [DecidableEq α]
    (G : Finset α) (Q : Three → Finset α) (x : α) : ℤ :=
  (((2 ^ G.card : ℕ) : ℤ) *
      (codeDeficit (canonicalCode (Q 2)) x + 1) - 1) *
      channelWeight Q 0 * channelWeight Q 1 - 1

private def deltaQZero {α : Type*} [DecidableEq α]
    (G : Finset α) (Q : Three → Finset α) (x : α) : ℤ :=
  (2 * codeDeficit (canonicalCode (Q 0)) x + 1) *
      channelWeight Q 1 * gChannelWeight G Q - 1

private def deltaQOne {α : Type*} [DecidableEq α]
    (G : Finset α) (Q : Three → Finset α) (x : α) : ℤ :=
  (2 * codeDeficit (canonicalCode (Q 1)) x + 1) *
      channelWeight Q 0 * gChannelWeight G Q - 1

private def sizeDeltaG (b : ℕ) : ℤ :=
  ((4 * 2 ^ b * (2 ^ b + 1) : ℕ) : ℤ)

private def sizeDeltaQTwo (b : ℕ) : ℤ :=
  -(sizeDeltaG b + 2)

private def sizeAnchor (b : ℕ) : ℤ :=
  (((2 ^ (b + 1) + 1) * (2 ^ b * 2 ^ b + 1) : ℕ) : ℤ) - 1

private def sizeDeltaQAnchor (b : ℕ) : ℤ :=
  -(sizeAnchor b + 2)

/-- Claim 22658: the punctured-cube optional codes have deficit `-1` at
 every block coordinate; in the exact six-channel repair, equal block size
 gives the displayed positive-anchor and two-unit-reversal deficits, with
 the `G` coordinate growing positive while the `Q₂` coordinate grows more
 negative as the common block size increases. -/
def claim22658 : Prop :=
  (∀ {α : Type*} [DecidableEq α]
    (G : Finset α) (Q : Three → Finset α) (b : ℕ),
    canonicalBlocks G Q b →
      (∀ i : Three, ∀ x ∈ Q i,
        codeDeficit (canonicalCode (Q i)) x = -1 ∧
          codeDeficit (canonicalCode (Q i)) x < 0) ∧
      deltaG Q = sizeDeltaG b ∧
      (∀ x ∈ Q 2, deltaQTwo G Q x = -(deltaG Q + 2)) ∧
      0 < anchorZeroDeficit G Q ∧
      0 < anchorOneDeficit G Q ∧
      (∀ x ∈ Q 0,
        deltaQZero G Q x = -(anchorZeroDeficit G Q + 2)) ∧
      (∀ x ∈ Q 1,
        deltaQOne G Q x = -(anchorOneDeficit G Q + 2))) ∧
  (∀ b b' : ℕ, 1 ≤ b → b ≤ b' →
    sizeDeltaG b ≤ sizeDeltaG b' ∧
      sizeDeltaQTwo b' ≤ sizeDeltaQTwo b ∧
      sizeDeltaQTwo b' < 0 ∧
      sizeAnchor b ≤ sizeAnchor b' ∧
      sizeDeltaQAnchor b' ≤ sizeDeltaQAnchor b)

end

end MathlibPlus.Open.ResearchFormalization.Claim22658CanonicalSeparatingBlocks
