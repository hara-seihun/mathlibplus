import Mathlib
import MathlibPlus.Open.Research.FormalizationBatch_01a004d6

namespace MathlibPlus.Open.Research.FormalizationBatch.R2003MinimumIntersection

open MathlibPlus.Open.Research.FormalizationBatch

/-- A selected pair realizes the smallest allowed intersection value. -/
def smallestAllowedMinimumPair {α : Type*} [DecidableEq α]
    (L : Finset ℕ) (F : Finset (Finset α))
    (ell : ℕ) (A B : Finset α) : Prop :=
  A ∈ F ∧ B ∈ F ∧ A ≠ B ∧
    ell ∈ L ∧ (∀ q ∈ L, ell ≤ q) ∧
    (A ∩ B).card = ell ∧
    ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → ell ≤ (X ∩ Y).card

/-- The realized pair-intersection cardinalities of a finite family. -/
def pairIntersectionSpectrum {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Finset ℕ :=
  F.biUnion (fun A => (F.erase A).image (fun B => (A ∩ B).card))

/-- The `(ell+1)`-subsets of the union of a selected minimum pair. -/
def minimumPairCover {α : Type*} [DecidableEq α]
    (M : Finset α) (ell : ℕ) : Finset (Finset α) :=
  M.powerset.filter (fun T => T.card = ell + 1)

/-- The class assigned to a covering set by a chosen class index. -/
def chosenCoverClass {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (choice : Finset α → Finset α)
    (T : Finset α) : Finset (Finset α) :=
  F.filter (fun C => choice C = T)

/-- A choice of a covering index partitions the original family. -/
def isChosenCoverPartition {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α) (ell : ℕ)
    (choice : Finset α → Finset α) : Prop :=
  (∀ C ∈ F,
      choice C ∈ minimumPairCover M ell ∧ choice C ⊆ C) ∧
    F = (minimumPairCover M ell).biUnion (chosenCoverClass F choice) ∧
    (∀ T₁ ∈ minimumPairCover M ell, ∀ T₂ ∈ minimumPairCover M ell,
      T₁ ≠ T₂ → Disjoint (chosenCoverClass F choice T₁)
        (chosenCoverClass F choice T₂))

/-- Delete the selected common subset from one chosen class. -/
def deletedChosenCoverClass {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (choice : Finset α → Finset α)
    (T : Finset α) : Finset (Finset α) :=
  (chosenCoverClass F choice T).image (fun C => C \ T)

/-- Every residual intersection value is the shifted value of a larger old one. -/
def residualSpectrumShifted {α : Type*} [DecidableEq α]
    (L : Finset ℕ) (ell : ℕ)
    (F : Finset (Finset α)) (choice : Finset α → Finset α)
    (T : Finset α) : Prop :=
  ∀ k ∈ pairIntersectionSpectrum (deletedChosenCoverClass F choice T),
    ∃ q ∈ pairIntersectionSpectrum F,
      q ∈ L.erase ell ∧ k = q - (ell + 1)

/-- Claim 35171: the minimum-intersection cover and deletion step. -/
def claim35171 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (L : Finset ℕ) (s n : ℕ) (F : Finset (Finset α)),
    1 < s →
    claim35168_exactFixedIntersectionSpectrum α n s L F →
    ∃ (ell : ℕ) (A B : Finset α) (choice : Finset α → Finset α),
      smallestAllowedMinimumPair L F ell A B ∧
      (∀ C ∈ F, ell < (C ∩ (A ∪ B)).card) ∧
      isChosenCoverPartition F (A ∪ B) ell choice ∧
      (∀ T ∈ minimumPairCover (A ∪ B) ell,
        let G := deletedChosenCoverClass F choice T
        uniformFamily G (n - (ell + 1)) ∧
        sunflowerFree G ∧
        residualSpectrumShifted L ell F choice T ∧
        (pairIntersectionSpectrum G).card ≤ s - 1)

end MathlibPlus.Open.Research.FormalizationBatch.R2003MinimumIntersection
