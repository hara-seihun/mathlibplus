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

private def exactlyTwoAt {α : Type*} [DecidableEq α]
    {s : ℕ} (R : Fin s → Finset α) (x : α)
    (i j k : Fin s) : Prop :=
  (if x ∈ R i then 1 else 0) +
      (if x ∈ R j then 1 else 0) +
      (if x ∈ R k then 1 else 0) = 2

private def witnessTripleCount {α : Type*} [DecidableEq α]
    {s : ℕ} (R : Fin s → Finset α) (x : α) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin s))).filter
    (fun e =>
      e.card = 3 ∧
        (e.filter (fun i : Fin s => x ∈ R i)).card = 2)).card

private def forbiddenDeficit (s : ℕ) : ℚ :=
  (Nat.choose s 3 : ℚ) -
    ((s - 2 : ℕ) : ℚ) / 2 * (s ^ 2 / 4 : ℕ)

/-- Claim 34928: in the finite indexed colored residual occurrence system,
unequal pairwise intersections have exactly-two witnesses, forbidden color
patterns have such witnesses, and the resulting integral incidence and
second-moment inequalities hold. -/
def claim34928 : Prop :=
  ∀ (α β : Type*) [DecidableEq α] [DecidableEq β]
    (s r : ℕ) (R : Fin s → Finset α) (color : Fin s → β),
    0 < s →
    (∀ i : Fin s, (R i).card = r) ∧
      (∀ i j : Fin s, i ≠ j → (R i ∩ R j).Nonempty) ∧
      Function.Injective (fun i : Fin s => (color i, R i)) ∧
      (colorRange color).card ≤ r + 1 ∧
      (¬ ∃ i j k : Fin s,
        residualSunflower R i j k ∧
          forbiddenColorTriple color i j k) →
      (∀ i j k : Fin s, distinctTriple i j k →
        ((¬ residualSunflower R i j k) ↔
          ∃ x : α, exactlyTwoAt R x i j k)) ∧
      (∀ i j k : Fin s,
        forbiddenColorTriple color i j k →
          ∃ x : α, exactlyTwoAt R x i j k) ∧
      (∀ x : α, x ∈ residualGround R →
        witnessTripleCount R x =
          Nat.choose (residualDegree R x) 2 *
            (s - residualDegree R x)) ∧
      forbiddenDeficit s ≤
        ((∑ x ∈ residualGround R,
          Nat.choose (residualDegree R x) 2 *
            (s - residualDegree R x) : ℕ) : ℚ) ∧
      (2 * forbiddenDeficit s / (s : ℚ)) ≤
        ∑ x ∈ residualGround R,
          (residualDegree R x : ℚ) *
            ((residualDegree R x : ℚ) - 1)

end

end MathlibPlus.Open.Combinatorics.AdmittedBatchR1913
