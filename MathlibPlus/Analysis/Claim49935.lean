import MathlibPlus.Basic

namespace MathlibPlus.Analysis

/-- Claim 49935's finite independent-sign query-cost replay.  The address-first
policy always uses the address and then its selected leaf; if the leaf is
queried first, the plus branch costs two queries and the minus branch costs
three.  The expectation is taken over all three independent fair signs. -/
theorem claim49935_policyCosts (n : ℕ) (_hn : 1 ≤ n) (_i : Fin n) :
    let target : Fin 2 → Fin 2 → Fin 2 → Fin 2 :=
      fun a y z => if a = 0 then y else z
    let addressFirstCost : Fin 2 → Fin 2 → Fin 2 → ℚ := fun _ _ _ => 2
    let leafFirstCost : Fin 2 → Fin 2 → Fin 2 → ℚ :=
      fun a _ _ => if a = 0 then 2 else 3
    let denominator : ℚ :=
      Fintype.card (Fin 2) * Fintype.card (Fin 2) * Fintype.card (Fin 2)
    let addressFirstExpectation : ℚ :=
      (∑ a : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2,
        addressFirstCost a y z) / denominator
    let leafFirstExpectation : ℚ :=
      (∑ a : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2,
        leafFirstCost a y z) / denominator
    target 0 0 1 = 0 ∧ target 1 0 1 = 1 ∧
      addressFirstExpectation = 2 ∧
      leafFirstExpectation = 5 / 2 ∧
      (2 : ℚ) < 5 / 2 := by
  norm_num [Fintype.card_fin, Fin.sum_univ_succ]

end MathlibPlus.Analysis
