import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.R1913Claim34930

noncomputable section

private def threeSunflower {α : Type*} [DecidableEq α]
    (X Y Z : Finset α) : Prop :=
  X ∩ Y = X ∩ Z ∧ X ∩ Y = Y ∩ Z

private def sourceUniform {α : Type*}
    (F : Finset (Finset α)) (n : ℕ) : Prop :=
  ∀ X ∈ F, X.card = n

private def sourcePairwiseIntersecting {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → (X ∩ Y).Nonempty

private def sourceThreeSunflowerFree {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ X ∈ F, ∀ Y ∈ F, ∀ Z ∈ F,
    X ≠ Y → X ≠ Z → Y ≠ Z →
      ¬ threeSunflower X Y Z

private def residualSunflower {α : Type*} [DecidableEq α]
    {s : ℕ} (R : Fin s → Finset α) (i j k : Fin s) : Prop :=
  R i ∩ R j = R i ∩ R k ∧ R i ∩ R k = R j ∩ R k

private def oneColor {α : Type*} [DecidableEq α]
    {s : ℕ} (color : Fin s → α) (i j k : Fin s) : Prop :=
  color i = color j ∧ color i = color k

private def threeColors {α : Type*} [DecidableEq α]
    {s : ℕ} (color : Fin s → α) (i j k : Fin s) : Prop :=
  color i ≠ color j ∧ color i ≠ color k ∧ color j ≠ color k

private def forbiddenColorTriple {α : Type*} [DecidableEq α]
    {s : ℕ} (color : Fin s → α) (i j k : Fin s) : Prop :=
  i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    (oneColor color i j k ∨ threeColors color i j k)

private def colorRange {α : Type*} [DecidableEq α]
    {s : ℕ} (color : Fin s → α) : Finset α :=
  (Finset.univ : Finset (Fin s)).image color

private def residualGround {α : Type*} [DecidableEq α]
    {s : ℕ} (R : Fin s → Finset α) : Finset α :=
  (Finset.univ : Finset (Fin s)).biUnion R

private def residualDegree {α : Type*} [DecidableEq α]
    {s : ℕ} (R : Fin s → Finset α) (x : α) : ℕ :=
  (Finset.univ.filter (fun i : Fin s => x ∈ R i)).card

private def residualSystem {α : Type*} [DecidableEq α]
    {s r : ℕ} (R : Fin s → Finset α) (color : Fin s → α) : Prop :=
  0 < s ∧
    (∀ i : Fin s, (R i).card = r) ∧
    (∀ i j : Fin s, i ≠ j → (R i ∩ R j).Nonempty) ∧
    Function.Injective (fun i : Fin s => (color i, R i)) ∧
    (colorRange color).card ≤ r + 1 ∧
    ¬ ∃ i j k : Fin s,
      residualSunflower R i j k ∧
        forbiddenColorTriple color i j k

private def sourceSingletonTraceSystem {α : Type*} [DecidableEq α]
    (n s r : ℕ) (F : Finset (Finset α)) (A : Finset α)
    (B : Fin s → Finset α) (color : Fin s → α)
    (R : Fin s → Finset α) : Prop :=
  A ∈ F ∧
    sourceUniform F n ∧
    sourcePairwiseIntersecting F ∧
    sourceThreeSunflowerFree F ∧
    (∀ i : Fin s,
      B i ∈ F ∧
        color i ∈ A ∧
        A ∩ B i = {color i} ∧
        R i = B i \ A ∧
        (R i).card = r) ∧
    r = n - 1 ∧
    residualSystem (r := r) R color

private def heavyCoordinates {α : Type*} [DecidableEq α]
    {s : ℕ} (D : ℕ) (R : Fin s → Finset α) : Finset α :=
  (residualGround R).filter (fun x => D < residualDegree R x)

private def traceOnHeavy {α : Type*} [DecidableEq α]
    {s : ℕ} (D : ℕ) (R : Fin s → Finset α) (i : Fin s) : Finset α :=
  R i ∩ heavyCoordinates D R

private def traceClass {α : Type*} [DecidableEq α]
    {s : ℕ} (D : ℕ) (R : Fin s → Finset α) (T : Finset α) : Finset (Fin s) :=
  (Finset.univ : Finset (Fin s)).filter
    (fun i => traceOnHeavy D R i = T)

private def classResiduals {α : Type*} [DecidableEq α]
    {s : ℕ} (R : Fin s → Finset α) (T : Finset α) : Fin s → Finset α :=
  fun i => R i \ T

private def classDegree {α : Type*} [DecidableEq α]
    {s : ℕ} (D : ℕ) (R : Fin s → Finset α) (T : Finset α) (x : α) : ℕ :=
  ((traceClass D R T).filter (fun i => x ∈ R i)).card

private def recordEightBound (D r : ℕ) : ℕ :=
  max 7 (96 * (D - 1) * r)

/-- Claim 34930: for a valid singleton-trace residual system and D≥1,
partitioning by the exact heavy-coordinate trace gives the stated trace
count, classwise residual uniformity and forbidden-color preservation, the
class degree bound, and the classwise Record-8 size estimate. -/
def claim34930 : Prop :=
  ∀ (α : Type*) [DecidableEq α]
    (n s r D β : ℕ)
    (F : Finset (Finset α)) (A : Finset α)
    (B : Fin s → Finset α) (color : Fin s → α)
    (R : Fin s → Finset α),
    1 ≤ D →
    sourceSingletonTraceSystem n s r F A B color R →
      let H := heavyCoordinates D R
      let traces := (Finset.univ : Finset (Fin s)).image
        (traceOnHeavy D R)
      H.card ≤ β * r →
        traces.card ≤ 2 ^ (β * r) ∧
          (∀ T ∈ traces,
            let I := traceClass D R T
            I.Nonempty ∧
              (∀ i ∈ I,
                (classResiduals R T i).card = r - T.card) ∧
              (∀ x : α, x ∉ T → classDegree D R T x ≤ D) ∧
              (∀ i j k : Fin s,
                i ∈ I → j ∈ I → k ∈ I →
                  residualSunflower (classResiduals R T) i j k →
                    ¬ forbiddenColorTriple color i j k) ∧
              I.card ≤ recordEightBound D r) ∧
          s ≤ recordEightBound D r * 2 ^ (β * r)

end

end MathlibPlus.Open.Combinatorics.R1913Claim34930
