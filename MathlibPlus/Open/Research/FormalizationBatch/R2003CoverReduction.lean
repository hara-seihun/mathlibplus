import Mathlib
import MathlibPlus.Open.Research.FormalizationBatch_01a004d6

namespace MathlibPlus.Open.Research.FormalizationBatch.R2003CoverReduction

open MathlibPlus.Open.Research.FormalizationBatch

/-- The realized pair-intersection cardinalities of a finite family. -/
def pairIntersectionSpectrum {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Finset ℕ :=
  F.biUnion (fun A => (F.erase A).image (fun B => (A ∩ B).card))

/-- A selected pair realizes the smallest allowed intersection value. -/
def smallestAllowedMinimumPair {α : Type*} [DecidableEq α]
    (L : Finset ℕ) (F : Finset (Finset α))
    (ell : ℕ) (A B : Finset α) : Prop :=
  A ∈ F ∧ B ∈ F ∧ A ≠ B ∧
    ell ∈ L ∧ (∀ q ∈ L, ell ≤ q) ∧
    (A ∩ B).card = ell ∧
    ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → ell ≤ (X ∩ Y).card

/-- The covering `(ell+1)`-subsets of a chosen pair union. -/
def minimumPairCover {α : Type*} [DecidableEq α]
    (M : Finset α) (ell : ℕ) : Finset (Finset α) :=
  M.powerset.filter (fun T => T.card = ell + 1)

/-- The class assigned to a covering set by a chosen index. -/
def chosenCoverClass {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (choice : Finset α → Finset α)
    (T : Finset α) : Finset (Finset α) :=
  F.filter (fun C => choice C = T)

/-- A chosen index gives the stated disjoint cover by classes. -/
def isChosenCoverPartition {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α) (ell : ℕ)
    (choice : Finset α → Finset α) : Prop :=
  (∀ C ∈ F,
      choice C ∈ minimumPairCover M ell ∧ choice C ⊆ C) ∧
    F = (minimumPairCover M ell).biUnion (chosenCoverClass F choice) ∧
    (∀ T₁ ∈ minimumPairCover M ell, ∀ T₂ ∈ minimumPairCover M ell,
      T₁ ≠ T₂ → Disjoint (chosenCoverClass F choice T₁)
        (chosenCoverClass F choice T₂))

/-- Delete the chosen common subset from one cover class. -/
def deletedChosenCoverClass {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (choice : Finset α → Finset α)
    (T : Finset α) : Finset (Finset α) :=
  (chosenCoverClass F choice T).image (fun C => C \ T)

/-- The residual spectrum is obtained by shifting values above the minimum. -/
def residualSpectrumShifted {α : Type*} [DecidableEq α]
    (L : Finset ℕ) (ell : ℕ)
    (F : Finset (Finset α)) (choice : Finset α → Finset α)
    (T : Finset α) : Prop :=
  ∀ k ∈ pairIntersectionSpectrum (deletedChosenCoverClass F choice T),
    ∃ q ∈ pairIntersectionSpectrum F,
      q ∈ L.erase ell ∧ k = q - (ell + 1)

/-- Claim 35172: cover, partition, deletion, and the induction recurrence. -/
def claim35172 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (L : Finset ℕ) (s n : ℕ) (F : Finset (Finset α)),
    1 < s →
    claim35168_exactFixedIntersectionSpectrum α n s L F →
    ∃ (ell : ℕ) (A B : Finset α) (choice : Finset α → Finset α),
      smallestAllowedMinimumPair L F ell A B ∧
      (∀ C ∈ F, ell < (C ∩ (A ∪ B)).card) ∧
      (∀ C ∈ F, ∃ T : Finset α,
        T ⊆ A ∪ B ∧ T.card = ell + 1 ∧ T ⊆ C) ∧
      isChosenCoverPartition F (A ∪ B) ell choice ∧
      (minimumPairCover (A ∪ B) ell).card ≤
        Nat.choose (A ∪ B).card (ell + 1) ∧
      (∀ T ∈ minimumPairCover (A ∪ B) ell,
        let G := deletedChosenCoverClass F choice T
        uniformFamily G (n - (ell + 1)) ∧
        sunflowerFree G ∧
        residualSpectrumShifted L ell F choice T ∧
        (pairIntersectionSpectrum G).card ≤ s - 1) ∧
      (F.card : ℝ) ≤
        ((n ^ 2 - n + 2 : ℕ) : ℝ) *
          (8 : ℝ) ^ (s - 1) *
          Real.rpow (2 : ℝ)
            (((1 : ℝ) + Real.sqrt 5 / 5) * (n : ℝ) *
              ((s - 1 : ℕ) : ℝ))

end MathlibPlus.Open.Research.FormalizationBatch.R2003CoverReduction
