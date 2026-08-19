import Mathlib

namespace MathlibPlus.Open.Order.Claim20937

/-- Claim 20937: when the two endpoints collapse, no element can lie between
 the equal lower and upper endpoints. -/
def claim20937 : Prop :=
  ∀ {α : Type*} [Preorder α] (p q : α),
    p = q →
      ∀ r : α, ¬ (p ≤ r ∧ r < q)

end MathlibPlus.Open.Order.Claim20937
