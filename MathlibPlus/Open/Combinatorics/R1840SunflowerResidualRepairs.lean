import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.R1840

noncomputable section

private def cellCount {α : Type*} [DecidableEq α]
    (U : Finset α) (A : Fin 3 → Finset α)
    (S : Finset (Fin 3)) : ℕ :=
  (U.filter (fun u =>
    ∀ i : Fin 3, (i ∈ S ↔ u ∈ A i))).card

private def properMargin {α : Type*} [DecidableEq α]
    (U : Finset α) (A : Fin 3 → Finset α)
    (T : Finset (Fin 3)) : ℕ :=
  (U.filter (fun u => ∀ i ∈ T, u ∈ A i)).card

private def tripleOf {α : Type*}
    (A₀ A₁ A₂ : Finset α) : Fin 3 → Finset α :=
  fun i =>
    if i = (0 : Fin 3) then A₀ else
      if i = (1 : Fin 3) then A₁ else A₂

private def pairwiseDistinctTriple {α : Type*}
    (A : Fin 3 → Finset α) : Prop :=
  ∀ ⦃i j : Fin 3⦄, i ≠ j → A i ≠ A j

private def threeSunflower {α : Type*} [DecidableEq α]
    (A : Fin 3 → Finset α) : Prop :=
  ∃ C : Finset α,
    ∀ ⦃i j : Fin 3⦄, i ≠ j → A i ∩ A j = C

private def primitiveTrade (S : Finset (Fin 3)) : ℤ :=
  (-1 : ℤ) ^ (3 - S.card)

private def cellTableDifference {α : Type*} [DecidableEq α]
    (U : Finset α) (A B : Fin 3 → Finset α)
    (S : Finset (Fin 3)) : ℤ :=
  (cellCount U A S : ℤ) - cellCount U B S

private def uniformFamily {α : Type*}
    (F : Set (Set α)) (n : ℕ) : Prop :=
  ∀ B, B ∈ F → B.Finite ∧ Set.ncard B = n

private def sunflowerFamily {α : Type*}
    (F : Set (Set α)) : Prop :=
  ∃ C : Set α,
    ∀ ⦃B₁ B₂ : Set α⦄,
      B₁ ∈ F → B₂ ∈ F → B₁ ≠ B₂ → B₁ ∩ B₂ = C

private def sunflowerFree {α : Type*}
    (F : Set (Set α)) (k : ℕ) : Prop :=
  ¬ ∃ S : Set (Set α),
      S.Finite ∧ Set.ncard S = k ∧ S ⊆ F ∧ sunflowerFamily S

private def exactTraceResidual {α : Type*}
    (F : Set (Set α)) (A T : Set α) : Set (Set α) :=
  (fun B : Set α => B \ A) ''
    {B | B ∈ F ∧ B ≠ A ∧ A ∩ B = T}

/-- The explicit finite witness in the proper-margin fiber obstruction. -/
def realizableSunflowerNonSunflowerFiberWitness_claim32802 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (n : ℕ) (C : Finset α) (a b c d : α),
    2 ≤ n →
    C.card = n - 2 →
    a ∉ C → b ∉ C → c ∉ C → d ∉ C →
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    let U := C ∪ {a, b, c, d}
    let A : Fin 3 → Finset α :=
      tripleOf (C ∪ {a, b}) (C ∪ {a, c}) (C ∪ {a, d})
    let B : Fin 3 → Finset α :=
      tripleOf (C ∪ {a, b}) (C ∪ {a, c}) (C ∪ {b, c})
    U.card = n + 2 ∧
      (∀ i : Fin 3,
        A i ⊆ U ∧ B i ⊆ U ∧
          (A i).card = n ∧ (B i).card = n) ∧
      pairwiseDistinctTriple A ∧ pairwiseDistinctTriple B ∧
      (∀ i : Fin 3,
        properMargin U A {i} = n ∧
          properMargin U B {i} = n) ∧
      (∀ ⦃i j : Fin 3⦄, i ≠ j →
        properMargin U A {i, j} = n - 1 ∧
          properMargin U B {i, j} = n - 1) ∧
      threeSunflower A ∧
      (∀ ⦃i j : Fin 3⦄, i ≠ j →
        A i ∩ A j = C ∪ {a}) ∧
      ¬ threeSunflower B ∧
      B 0 ∩ B 1 = C ∪ {a} ∧
      B 0 ∩ B 2 = C ∪ {b} ∧
      B 1 ∩ B 2 = C ∪ {c} ∧
      (∀ S : Finset (Fin 3),
        cellTableDifference U A B S = primitiveTrade S)

/-- The exact-trace residual family of a fixed member. -/
def residualSunflowerFreeness_claim32807 : Prop :=
  ∀ {α : Type*}
    (F : Set (Set α)) (n k : ℕ),
    uniformFamily F n → sunflowerFree F k →
    ∀ A, A ∈ F →
      ∀ T : Set α, T ⊂ A →
        sunflowerFree (exactTraceResidual F A T) k

/-- A residual family has no matching of size `k - 1`, i.e. its matching
number is at most `k - 2` in the stated sunflower parameterization. -/
def residualMatchingNumberGain_claim32808 : Prop :=
  ∀ {α : Type*}
    (F : Set (Set α)) (n k : ℕ),
    uniformFamily F n → sunflowerFree F k →
    ∀ A, A ∈ F →
      ∀ T : Set α, T ⊂ A →
        ¬ ∃ R : Fin (k - 1) → Set α,
          (∀ i : Fin (k - 1),
            R i ∈ exactTraceResidual F A T) ∧
          (∀ ⦃i j : Fin (k - 1)⦄, i ≠ j → R i ≠ R j) ∧
          (∀ ⦃i j : Fin (k - 1)⦄, i ≠ j →
            Disjoint (R i) (R j))

end

end MathlibPlus.Open.Combinatorics.R1840
