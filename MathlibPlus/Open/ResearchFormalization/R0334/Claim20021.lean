import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0334.Claim20021

open scoped BigOperators

noncomputable def productChoices {k : Type*} [Fintype k]
    {α : Type*} [DecidableEq α]
    (C : k → Finset (Finset α)) : Finset (∀ i, C i) :=
  letI : ∀ i, Fintype (C i) := fun i => Fintype.ofFinite _
  letI : Fintype (∀ i, C i) := Fintype.ofFinite _
  Finset.univ

def productUnionMap {k : Type*} [Fintype k]
    {α : Type*} [DecidableEq α]
    (C : k → Finset (Finset α)) (choice : ∀ i, C i) : Finset α :=
  Finset.univ.biUnion (fun i => (choice i : Finset α))

noncomputable def productFamily {k : Type*} [Fintype k]
    {α : Type*} [DecidableEq α]
    (C : k → Finset (Finset α)) : Finset (Finset α) :=
  (productChoices C).image (productUnionMap C)

def injectiveProduct {k : Type*} [Fintype k]
    {α : Type*} [DecidableEq α]
    (C : k → Finset (Finset α)) : Prop :=
  Function.Injective (productUnionMap C)

def productSize {k : Type*} [Fintype k]
    {α : Type*} [DecidableEq α]
    (C : k → Finset (Finset α)) : ℕ :=
  ∏ i, (C i).card

def factorHasEmpty {k : Type*} [Fintype k]
    {α : Type*} [DecidableEq α]
    (C : k → Finset (Finset α)) : Prop :=
  ∀ i, ∅ ∈ C i

def factorUnionClosed {k : Type*} [Fintype k]
    {α : Type*} [DecidableEq α]
    (C : k → Finset (Finset α)) : Prop :=
  ∀ i A B, A ∈ C i → B ∈ C i → A ∪ B ∈ C i

def familySupport {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Finset α :=
  F.biUnion (fun A => A)

def disjointFactorSupports {k : Type*} [Fintype k]
    {α : Type*} [DecidableEq α]
    (C : k → Finset (Finset α)) : Prop :=
  ∀ i j, i ≠ j → Disjoint (familySupport (C i)) (familySupport (C j))

noncomputable def puncturedProduct {k : Type*} [Fintype k]
    {α : Type*} [DecidableEq α]
    (C : k → Finset (Finset α)) : Finset (Finset α) :=
  (productFamily C).filter (fun A => A ≠ ∅)

def deficitProduct {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x : α) : ℤ :=
  (F.card : ℤ) - 2 * ((F.filter (fun A => x ∈ A)).card : ℤ)

def nontrivialFactorCount {k : Type*} [Fintype k]
    {α : Type*} [DecidableEq α]
    (C : k → Finset (Finset α)) : ℕ :=
  (Finset.univ.filter (fun i => (C i).card > 1)).card

def disjointSupportDeficitScaling_claim20021 : Prop :=
  ∀ (k : ℕ) (n : ℕ) (C : Fin k → Finset (Finset (Fin n))),
    factorHasEmpty C →
    factorUnionClosed C →
    injectiveProduct C →
    disjointFactorSupports C →
    (∀ i : Fin k, ∀ x : Fin n, x ∈ familySupport (C i) →
      let P := productFamily C
      let Ppunct := puncturedProduct C
      let N := productSize C
      let ni := (C i).card
      P.card = N ∧
        deficitProduct P x = ((N / ni : ℕ) : ℤ) * deficitProduct (C i) x ∧
        deficitProduct Ppunct x = ((N / ni : ℕ) : ℤ) * deficitProduct (C i) x - 1) ∧
    (nontrivialFactorCount C ≥ 2 →
      ((∀ x : Fin n, x ∈ familySupport (productFamily C) →
          0 < deficitProduct (puncturedProduct C) x) ↔
        (∀ i : Fin k, (C i).card > 1 →
          ∀ x : Fin n, x ∈ familySupport (C i) →
            0 < deficitProduct (C i) x)))

end MathlibPlus.Open.ResearchFormalization.R0334.Claim20021
