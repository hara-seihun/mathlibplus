import MathlibPlus.Open.Formalization.BatchUnionClosed

open scoped BigOperators

namespace MathlibPlus.Open.Research.R2672

/-- Claim 47192: the trace-fibre deficit ledger for a finite ordinary
union-closed family with a selected three-element member. -/
def claim47192 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (M : Finset α),
    M ∈ F →
    M.card = 3 →
    MathlibPlus.Open.ordinaryUnionClosed F →
    let H : Finset α → Finset (Finset α) :=
      fun S =>
        (F.filter (fun A => A \ M = S)).image (fun A => A ∩ M)
    let supportFamily : Finset (Finset α) :=
      F.image (fun A => A \ M)
    let neutralSupports : Finset (Finset α) :=
      supportFamily.filter (fun S => H S = {∅, M})
    let otherSupports : Finset (Finset α) :=
      supportFamily.filter (fun S => H S ≠ {∅, M})
    (∀ S : Finset α, S ∈ supportFamily ↔ (H S).Nonempty) ∧
    (∀ S : Finset α, (H S).Nonempty → M ∈ H S) ∧
    (∀ S : Finset α, H S = {M} → S ∈ otherSupports) ∧
    (∀ S : Finset α, S ∈ neutralSupports →
      ((H S).card : ℤ) - 2 = 0) ∧
    (∀ S : Finset α, H S = {M} →
      ((H S).card : ℤ) - 2 = -1) ∧
    (MathlibPlus.Open.principalFilterDeficit F M =
      supportFamily.sum (fun S => ((H S).card : ℤ) - 2)) ∧
    (MathlibPlus.Open.principalFilterDeficit F M = 13 →
      F.card = 2 * (neutralSupports.card + otherSupports.card) + 13 ∧
      supportFamily.card = neutralSupports.card + otherSupports.card)

end MathlibPlus.Open.Research.R2672
