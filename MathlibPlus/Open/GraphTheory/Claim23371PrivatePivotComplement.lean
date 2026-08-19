import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.GraphTheory.Claim23371

abbrev CardMultiset23371 (Card : Type*) := Card → ℕ

structure FiniteCardComplementSystem23371
    (Host Card : Type*) [Fintype Host] [Fintype Card] where
  hostComplement : Equiv.Perm Host
  cardComplement : Equiv.Perm Card
  cardMultiplicity : Card → Host → ℕ
  cardMultiplicity_complement :
    ∀ card host,
      cardMultiplicity (cardComplement card)
          (hostComplement host) =
        cardMultiplicity card host

private def complementCardMultiset23371
    {Card : Type*}
    (cardComplement : Equiv.Perm Card)
    (cards : CardMultiset23371 Card) : CardMultiset23371 Card :=
  fun card => cards (cardComplement.symm card)

private def complementHostFamily23371
    {Host : Type*} [DecidableEq Host]
    (hostComplement : Equiv.Perm Host)
    (family : Finset Host) : Finset Host :=
  family.image hostComplement

private def fallingCardMultiplicity23371
    {Host Card : Type*} [Fintype Card]
    (cardMultiplicity : Card → Host → ℕ)
    (cards : CardMultiset23371 Card)
    (host : Host) : ℕ :=
  ∏ card : Card,
    Nat.descFactorial
      (cardMultiplicity card host) (cards card)

private def familyPrivatePivot23371
    {Host Card : Type*}
    [Fintype Card] [DecidableEq Host]
    (cardMultiplicity : Card → Host → ℕ)
    (family : Finset Host)
    (cards : CardMultiset23371 Card)
    (host : Host) : Prop :=
  host ∈ family ∧
    fallingCardMultiplicity23371 cardMultiplicity cards host ≠ 0 ∧
    ∀ candidate ∈ family,
      fallingCardMultiplicity23371 cardMultiplicity cards candidate ≠ 0 →
        candidate = host

private def cardMultisetSize23371
    {Card : Type*} [Fintype Card]
    (cards : CardMultiset23371 Card) : ℕ :=
  ∑ card : Card, cards card

private def privatePeelingWitness23371
    {Host Card : Type*}
    [Fintype Host] [DecidableEq Host] [Fintype Card]
    (system : FiniteCardComplementSystem23371 Host Card)
    (family : Finset Host) (d waves : ℕ)
    (active : Fin (Nat.succ waves) → Finset Host)
    (pivots : Fin waves → CardMultiset23371 Card)
    (removed : Fin waves → Host) : Prop :=
  active 0 = family ∧
    active (Fin.last waves) = ∅ ∧
    ∀ w : Fin waves,
      removed w ∈ active w.castSucc ∧
      familyPrivatePivot23371 system.cardMultiplicity
        (active w.castSucc) (pivots w) (removed w) ∧
      cardMultisetSize23371 (pivots w) ≤ d ∧
      active w.succ = (active w.castSucc).erase (removed w)

def boundedPrivatePivotComplementClosed_claim23371 : Prop :=
  ∀ (Host Card : Type*) [Fintype Host] [DecidableEq Host] [Fintype Card],
    ∀ (system : FiniteCardComplementSystem23371 Host Card)
      (family : Finset Host) (d waves : ℕ)
      (active : Fin (Nat.succ waves) → Finset Host)
      (pivots : Fin waves → CardMultiset23371 Card)
      (removed : Fin waves → Host),
      privatePeelingWitness23371 system family d waves
        active pivots removed →
        privatePeelingWitness23371 system
          (complementHostFamily23371 system.hostComplement family)
          d waves
          (fun k => complementHostFamily23371 system.hostComplement (active k))
          (fun w =>
            complementCardMultiset23371 system.cardComplement (pivots w))
          (fun w => system.hostComplement (removed w))

end MathlibPlus.Open.GraphTheory.Claim23371

end
