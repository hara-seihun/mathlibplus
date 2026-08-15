import Mathlib

open scoped BigOperators
open BigOperators

namespace MathlibPlus.Open

noncomputable section

private abbrev ProperMarginIndex : Type :=
  {T : Finset (Fin 3) //
    T.Nonempty ∧ T ≠ (Finset.univ : Finset (Fin 3))}

private def cell {α : Type*} (U : Set α) (A : Fin 3 → Set α)
    (S : Finset (Fin 3)) : Set α :=
  {u | u ∈ U ∧ ∀ i : Fin 3, (i ∈ S ↔ u ∈ A i)}

private def cellCount {α : Type*} (U : Set α) (A : Fin 3 → Set α)
    (S : Finset (Fin 3)) : ℕ :=
  Set.ncard (cell U A S)

private def intersectionMargin {α : Type*} (A : Fin 3 → Set α)
    (T : Finset (Fin 3)) : ℕ :=
  Set.ncard {u | ∀ i ∈ T, u ∈ A i}

private def properMarginStatistic {α : Type*} (U : Set α)
    (A : Fin 3 → Set α) : ℕ × (ProperMarginIndex → ℕ) :=
  (Set.ncard U, fun T => intersectionMargin A T.1)

/-- The cell table and the proper-margin statistic for an ordered triple. -/
def cellTableAndProperMarginMap : Prop :=
  ∀ {α : Type*} (U : Set α), U.Finite →
    ∀ (A : Fin 3 → Set α), (∀ i : Fin 3, A i ⊆ U) →
      (∀ (T : Finset (Fin 3)), T.Nonempty →
        T ≠ (Finset.univ : Finset (Fin 3)) →
        intersectionMargin A T =
          Finset.sum ((Finset.univ : Finset (Finset (Fin 3))).filter
            (fun S => T ⊆ S)) (fun S => cellCount U A S)) ∧
      properMarginStatistic U A =
        (Set.ncard U, fun T => intersectionMargin A T.1)

private def orderedDistinctN {α : Type*} (U : Set α) (n : ℕ)
    (A : Fin 3 → Set α) : Prop :=
  U.Finite ∧
    (∀ i : Fin 3, A i ⊆ U ∧ Set.ncard (A i) = n) ∧
    (∀ ⦃i j : Fin 3⦄, i ≠ j → A i ≠ A j)

private def threeSunflower {α : Type*} (A : Fin 3 → Set α) : Prop :=
  ∃ C : Set α,
    ∀ ⦃i j : Fin 3⦄, i ≠ j → A i ∩ A j = C

/-- Proper margins have a fiber containing both sunflower and non-sunflower triples. -/
def properMarginsCannotDetectThreeSunflower : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∃ (α : Type) (U : Set α) (A B : Fin 3 → Set α),
      orderedDistinctN U n A ∧
      orderedDistinctN U n B ∧
      properMarginStatistic U A = properMarginStatistic U B ∧
      threeSunflower A ∧
      ¬ threeSunflower B ∧
      ∀ (β : Type) (h : (ℕ × (ProperMarginIndex → ℕ)) → β),
        h (properMarginStatistic U A) = h (properMarginStatistic U B)

private def sunflower {α : Type*} (S : Set (Set α)) : Prop :=
  ∃ C : Set α,
    ∀ ⦃B₁ B₂ : Set α⦄,
      B₁ ∈ S → B₂ ∈ S → B₁ ≠ B₂ → B₁ ∩ B₂ = C

private def nUniformFamily {α : Type*} (F : Set (Set α)) (n : ℕ) : Prop :=
  ∀ B, B ∈ F → B.Finite ∧ Set.ncard B = n

private def kSunflowerFree {α : Type*} (F : Set (Set α)) (k : ℕ) : Prop :=
  ¬ ∃ S : Set (Set α),
      S.Finite ∧ Set.ncard S = k ∧ S ⊆ F ∧ sunflower S

/-- Exact-trace residual families for a fixed member of a uniform sunflower-free family. -/
def fixedMemberExactTraceResidualConstruction : Prop :=
  ∀ {α : Type*} (F : Set (Set α)) (n k : ℕ),
    nUniformFamily F n →
    kSunflowerFree F k →
    ∀ A, A ∈ F →
      (¬ ∃ B, B ∈ F ∧ B ≠ A ∧ A ∩ B = A) ∧
      ∀ T : Set α, T ⊂ A →
        let F_T : Set (Set α) :=
          {B | B ∈ F ∧ B ≠ A ∧ A ∩ B = T}
        let R_T : Set (Set α) :=
          (fun B : Set α => B \ A) '' F_T
        (∀ B, B ∈ F_T →
          A ∩ B = T ∧ B \ A = B \ T) ∧
        (∀ R, R ∈ R_T → R.Finite ∧ Set.ncard R = n - Set.ncard T) ∧
        (∀ ⦃B₁ B₂ : Set α⦄,
          B₁ ∈ F_T → B₂ ∈ F_T → B₁ \ A = B₂ \ A → B₁ = B₂)

end

end MathlibPlus.Open
