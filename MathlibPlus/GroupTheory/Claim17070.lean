import Mathlib

namespace MathlibPlus.GroupTheory.Claim17070

/-- Claim 17070: the exact eight transport-subgroup orders. -/
theorem exactTransportSubgroupOrders_claim17070 :
    let orders : Fin 8 → ℕ := ![24, 16, 8, 12, 4, 12, 4, 4]
    orders 0 = 24 ∧ orders 1 = 16 ∧ orders 2 = 8 ∧ orders 3 = 12 ∧
      orders 4 = 4 ∧ orders 5 = 12 ∧ orders 6 = 4 ∧ orders 7 = 4 := by
  decide

end MathlibPlus.GroupTheory.Claim17070
