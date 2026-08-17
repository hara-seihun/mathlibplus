import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0392Claim20837

open scoped BigOperators

noncomputable section

/-- The exact trace multiplicity at a distinguished pivot. -/
def pivotTraceCount {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (A T : Finset α) : ℤ :=
  (F.filter (fun B => A ∩ B = T)).card

/-- The exact pivot-link multiplicity. -/
def pivotLinkCount {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (U : Finset α) : ℤ :=
  (F.filter (fun B => U ⊆ B)).card

/-- Claim 20837.  Both transforms use only subsets of the distinguished
pivot, which is the Boolean carrier fixed by the reviewed Claim 20838
formalization. -/
def exactPivotTraceAndLinkTransforms_claim20837 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (A : Finset α) (n : ℕ),
    A ∈ F →
    (∀ B ∈ F, B.card = n) →
      (∀ U : Finset α, U ⊆ A →
        pivotLinkCount F U =
          ∑ T ∈ A.powerset.filter (fun T => U ⊆ T),
            pivotTraceCount F A T) ∧
      (∀ T : Finset α, T ⊆ A →
        pivotTraceCount F A T =
          ∑ U ∈ A.powerset.filter (fun U => T ⊆ U),
            (-1 : ℤ) ^ (U.card - T.card) * pivotLinkCount F U)

end

end MathlibPlus.Open.ResearchFormalization.R0392Claim20837
