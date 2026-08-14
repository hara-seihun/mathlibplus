import Mathlib

namespace MathlibPlus.Open.Combinatorics.Claim3373

def ground {α : Type} [DecidableEq α] (F : Finset (Finset α)) : Finset α :=
  F.biUnion (fun A => A)

def frequency {α : Type} [DecidableEq α] (F : Finset (Finset α)) (x : α) : ℕ :=
  (F.filter (fun A => x ∈ A)).card

def unionClosed {α : Type} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ ⦃A B : Finset α⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

def franklCounterexample {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  2 ≤ F.card ∧ unionClosed F ∧
    ∀ x ∈ ground F, 2 * frequency F x < F.card

def minimumFranklCounterexample {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  franklCounterexample F ∧
    ∀ G : Finset (Finset α), franklCounterexample G → F.card ≤ G.card

def slack {α : Type} [DecidableEq α] (F : Finset (Finset α)) (x : α) : ℕ :=
  F.card - 2 * frequency F x

def tight {α : Type} [DecidableEq α] (F : Finset (Finset α)) (x : α) : Prop :=
  x ∈ ground F ∧ slack F x = 1

def atLeastThreeTightElements : Prop :=
  ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
    minimumFranklCounterexample F →
      ∃ x y z : α,
        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        tight F x ∧ tight F y ∧ tight F z ∧
        frequency F x = (F.card - 1) / 2 ∧
        frequency F y = (F.card - 1) / 2 ∧
        frequency F z = (F.card - 1) / 2

end MathlibPlus.Open.Combinatorics.Claim3373
