import Mathlib

open scoped BigOperators Classical
noncomputable section

namespace MathlibPlus.Open.Combinatorics.R1933Sharp

private def distinctUniformFamily {α : Type*} [DecidableEq α]
    {m n : ℕ} (F : Fin m → Finset α) : Prop :=
  Function.Injective F ∧ ∀ i : Fin m, (F i).card = n

private def coordinateSupport {α : Type*} [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) (x : α) : Finset (Fin m) :=
  Finset.univ.filter (fun i => x ∈ F i)

private def groundCoordinates {α : Type*} [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) : Finset α :=
  Finset.univ.biUnion (fun i => F i)

private def supportPatterns {α : Type*} [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) : Finset (Finset (Fin m)) :=
  (groundCoordinates F).image (coordinateSupport F) |>.filter
    (fun S => S.Nonempty)

private def laminarSupportFamily {m : ℕ}
    (S : Finset (Finset (Fin m))) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S,
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

private def pairwiseDisjointIndices {α : Type*} [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) (I : Finset (Fin m)) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (F i) (F j)

private def matchingNumber {α : Type*} [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) : ℕ :=
  (Finset.univ.powerset.filter (pairwiseDisjointIndices F)).sup Finset.card

private def indexedSunflower {α : Type*} [DecidableEq α]
    {m k : ℕ} (F : Fin m → Finset α) (I : Fin k → Fin m) : Prop :=
  Function.Injective I ∧
    ∃ C : Finset α,
      ∀ a b : Fin k, a ≠ b → F (I a) ∩ F (I b) = C

private def kSunflowerFree {α : Type*} [DecidableEq α]
    {m k : ℕ} (F : Fin m → Finset α) : Prop :=
  ¬∃ I : Fin k → Fin m, indexedSunflower F I

private def maximalSupports {m : ℕ}
    (S : Finset (Finset (Fin m))) : Finset (Finset (Fin m)) :=
  S.filter (fun A =>
    ∀ ⦃B : Finset (Fin m)⦄, B ∈ S → A ⊆ B → B = A)

/-- Claim 36327: literal incidence supports form the asserted sharp laminar
forest bound, with the per-index support count, per-root q-ary count, the
matching-number bound, and the sunflower-free corollary. -/
def sharpLaminarFamilyBound_claim36327 : Prop :=
  ∀ (α : Type*) [DecidableEq α]
    (m n k : ℕ) (F : Fin m → Finset α),
    distinctUniformFamily (n := n) F →
    1 ≤ n →
    3 ≤ k →
    kSunflowerFree (k := k) F →
    laminarSupportFamily (supportPatterns F) →
    (∀ i : Fin m,
      ((supportPatterns F).filter (fun S => i ∈ S)).card ≤ n) ∧
    (∀ R ∈ maximalSupports (supportPatterns F),
      R.card ≤ (k - 1) ^ (n - 1)) ∧
    m ≤ matchingNumber F * (k - 1) ^ (n - 1) ∧
    matchingNumber F ≤ k - 1 ∧
    m ≤ (k - 1) ^ n

end MathlibPlus.Open.Combinatorics.R1933Sharp
