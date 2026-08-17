import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0392Claim20838

private def pivotTraceCount {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (A T : Finset α) : ℤ :=
  (F.filter (fun B => A ∩ B = T)).card

private def pivotLinkCount {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (U : Finset α) : ℤ :=
  (F.filter (fun B => U ⊆ B)).card

/-- Claim 20838: in a distinct uniform family, the actual pivot supplies both
    endpoint cells of the Boolean trace table, so the proper pivot-link counts
    determine every exact pivot trace. -/
def actualPivotFixesFullBooleanCell_claim20838 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (A : Finset α) (n : ℕ),
    A ∈ F →
    (∀ B ∈ F, B.card = n) →
      pivotLinkCount F (∅ : Finset α) = (F.card : ℤ) ∧
        pivotLinkCount F A = 1 ∧
        ∀ T : Finset α, T ⊆ A →
          pivotTraceCount F A T =
            ∑ U ∈ A.powerset.filter (fun U => T ⊆ U),
              (-1 : ℤ) ^ (U.card - T.card) * pivotLinkCount F U

end MathlibPlus.Open.ResearchFormalization.R0392Claim20838
