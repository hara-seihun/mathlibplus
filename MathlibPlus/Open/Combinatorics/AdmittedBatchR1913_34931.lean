import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.AdmittedBatchR1913Claim34931

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

private def residualSystem {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s r : ℕ} (R : Fin s → Finset α) (color : Fin s → β) : Prop :=
  0 < s ∧
    (∀ i : Fin s, (R i).card = r) ∧
    (∀ i j : Fin s, i ≠ j → (R i ∩ R j).Nonempty) ∧
    Function.Injective (fun i : Fin s => (color i, R i)) ∧
    (colorRange color).card ≤ r + 1 ∧
    ¬ ∃ i j k : Fin s,
      residualSunflower R i j k ∧
        forbiddenColorTriple color i j k

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

private def incidenceSum {α : Type*} [DecidableEq α]
    {s : ℕ} (R : Fin s → Finset α) : ℕ :=
  (residualGround R).sum (fun x => residualDegree R x)

private def omittedIncidence {α : Type*} [DecidableEq α]
    {s : ℕ} (R : Fin s → Finset α) (H : Finset α) : ℕ :=
  H.sum (fun x => s - residualDegree R x)

private def traceCount {α : Type*} [DecidableEq α]
    {s : ℕ} (D : ℕ) (R : Fin s → Finset α) : ℕ :=
  (Finset.univ.image (traceOnHeavy D R)).card

private def recordEightBound (D r : ℕ) : ℕ :=
  max 7 (96 * (D - 1) * r)

private def mediumDegree {α : Type*} [DecidableEq α]
    {s : ℕ} (D E : ℕ) (R : Fin s → Finset α) (x : α) : Prop :=
  x ∈ residualGround R ∧
    D < residualDegree R x ∧ residualDegree R x < s - E

/-- Claim 34931: under the exact colored singleton-residual hypotheses, the
rare-or-near-common degree gap gives the heavy-coordinate size, omitted-
incidence trace count, classwise bounded-degree reduction, and the displayed
final size bound. -/
def claim34931 : Prop :=
  ∀ (α β : Type*) [DecidableEq α] [DecidableEq β]
    (s r D E : ℕ) (R : Fin s → Finset α) (color : Fin s → β),
    1 ≤ D →
    residualSystem (r := r) R color →
    (s > max (2 * E)
        (recordEightBound D r * (2 * E * r + 1)) →
      ∃ x : α, mediumDegree D E R x) ∧
    ((∀ x : α, x ∈ residualGround R →
        residualDegree R x ≤ D ∨ s - residualDegree R x ≤ E) →
      2 * E < s →
      let H := heavyCoordinates D R
      let q := traceCount D R
      let traces := Finset.univ.image (traceOnHeavy D R)
      incidenceSum R = s * r ∧
        (∀ x : α, x ∈ H →
          s - residualDegree R x ≤ E ∧
            s < 2 * residualDegree R x) ∧
        H.card < 2 * r ∧
        q - 1 ≤ omittedIncidence R H ∧
        omittedIncidence R H ≤ E * H.card ∧
        q ≤ 2 * E * r + 1 ∧
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
        s ≤ max (2 * E)
          (recordEightBound D r * (2 * E * r + 1)))

end

end MathlibPlus.Open.Combinatorics.AdmittedBatchR1913Claim34931
