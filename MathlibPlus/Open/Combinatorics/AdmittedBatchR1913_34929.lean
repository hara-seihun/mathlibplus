import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.AdmittedBatchR1913

noncomputable section

private def distinctTriple {s : ℕ} (i j k : Fin s) : Prop :=
  i ≠ j ∧ i ≠ k ∧ j ≠ k

private def residualSunflower {α : Type*} [DecidableEq α]
    {s : ℕ} (R : Fin s → Finset α) (i j k : Fin s) : Prop :=
  R i ∩ R j = R i ∩ R k ∧ R i ∩ R k = R j ∩ R k

private def oneColor {β : Type*} [DecidableEq β]
    {s : ℕ} (color : Fin s → β) (i j k : Fin s) : Prop :=
  color i = color j ∧ color i = color k

private def threeColors {β : Type*} [DecidableEq β]
    {s : ℕ} (color : Fin s → β) (i j k : Fin s) : Prop :=
  color i ≠ color j ∧ color i ≠ color k ∧ color j ≠ color k

private def forbiddenColorTriple {β : Type*} [DecidableEq β]
    {s : ℕ} (color : Fin s → β) (i j k : Fin s) : Prop :=
  distinctTriple i j k ∧
    (oneColor color i j k ∨ threeColors color i j k)

private def colorRange {β : Type*} [DecidableEq β]
    {s : ℕ} (color : Fin s → β) : Finset β :=
  (Finset.univ : Finset (Fin s)).image color

private def residualGround {α : Type*} [DecidableEq α]
    {s : ℕ} (R : Fin s → Finset α) : Finset α :=
  (Finset.univ : Finset (Fin s)).biUnion R

private def residualDegree {α : Type*} [DecidableEq α]
    {s : ℕ} (R : Fin s → Finset α) (x : α) : ℕ :=
  (Finset.univ.filter (fun i : Fin s => x ∈ R i)).card

private def forbiddenDeficit (s : ℕ) : ℚ :=
  (Nat.choose s 3 : ℚ) -
    ((s - 2 : ℕ) : ℚ) / 2 * (s ^ 2 / 4 : ℕ)

private def residualSystem {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s r : ℕ} (R : Fin s → Finset α) (color : Fin s → β) : Prop :=
  (∀ i : Fin s, (R i).card = r) ∧
    (∀ i j : Fin s, i ≠ j → (R i ∩ R j).Nonempty) ∧
    Function.Injective (fun i : Fin s => (color i, R i)) ∧
    (colorRange color).card ≤ r + 1 ∧
    ¬ ∃ i j k : Fin s,
      residualSunflower R i j k ∧
        forbiddenColorTriple color i j k

private def sourceSunflower {α : Type*} [DecidableEq α]
    (A B C : Finset α) : Prop :=
  A ∩ B = A ∩ C ∧ A ∩ C = B ∩ C

private def sourceUniform {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (n : ℕ) : Prop :=
  ∀ B ∈ 𝓕, B.card = n

private def sourcePairwiseIntersecting {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Prop :=
  ∀ ⦃B C : Finset α⦄, B ∈ 𝓕 → C ∈ 𝓕 → B ≠ C → (B ∩ C).Nonempty

private def sourceThreeSunflowerFree {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Prop :=
  ¬ ∃ A B C : Finset α,
    A ∈ 𝓕 ∧ B ∈ 𝓕 ∧ C ∈ 𝓕 ∧
      A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ sourceSunflower A B C

private def singletonPivotTraceSubsystem
    {α : Type*} [DecidableEq α]
    (n s r : ℕ) (𝓕 : Finset (Finset α)) (A : Finset α)
    (B : Fin s → Finset α) (color : Fin s → α)
    (R : Fin s → Finset α) : Prop :=
  0 < s ∧
    A ∈ 𝓕 ∧
    sourceUniform 𝓕 n ∧
    sourcePairwiseIntersecting 𝓕 ∧
    sourceThreeSunflowerFree 𝓕 ∧
    Function.Injective B ∧
    (∀ i : Fin s, (R i).card = r) ∧
    (∀ i : Fin s,
      B i ∈ 𝓕 ∧
        color i ∈ A ∧
        A ∩ B i = {color i} ∧
        R i = B i \ A)

/-- Claim 34929: bounded residual degrees give the stated integral witness
bound and singleton-trace size bound, while the full source-family context
identifies residual uniformity with `n - 1`. -/
def claim34929 : Prop :=
  (∀ (α β : Type*) [DecidableEq α] [DecidableEq β]
      (s r D : ℕ) (R : Fin s → Finset α) (color : Fin s → β),
    0 < s → residualSystem (r := r) R color →
      (∀ x : α, x ∈ residualGround R → residualDegree R x ≤ D) →
      (∑ x ∈ residualGround R, residualDegree R x) = s * r ∧
      ((∑ x ∈ residualGround R,
          (Nat.choose (residualDegree R x) 2 : ℚ) *
            (s - residualDegree R x)) ≤
        ((D - 1 : ℕ) : ℚ) * (r : ℚ) * (s : ℚ) ^ 2 / 2) ∧
      (8 ≤ s →
        (s : ℚ) ^ 3 / 192 ≤ forbiddenDeficit s) ∧
      (8 ≤ s → s ≤ 96 * (D - 1) * r) ∧
      s ≤ max 7 (96 * (D - 1) * r)) ∧
  (∀ (α : Type*) [DecidableEq α]
      (n s r : ℕ) (𝓕 : Finset (Finset α)) (A : Finset α)
      (B : Fin s → Finset α) (color : Fin s → α)
      (R : Fin s → Finset α),
    singletonPivotTraceSubsystem n s r 𝓕 A B color R →
      r = n - 1)

end

end MathlibPlus.Open.Combinatorics.AdmittedBatchR1913
