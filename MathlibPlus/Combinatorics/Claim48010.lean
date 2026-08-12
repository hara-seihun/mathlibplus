import Mathlib.Tactic

namespace MathlibPlus.Combinatorics.Claim48010

/-- Exact rational witness for the finite posterior-cell obstruction in packet
R-3560.  The decision-tree semantics are not silently reconstructed; the
source-provided first-query and path-revealment vectors, charge, variance, and
strict defect are recorded exactly. -/
theorem firstQueryRevealmentCounterexample :
    let p : Fin 3 → ℚ := fun i => if i = 0 then 0 else 1 / 2
    let r : Fin 3 → ℚ :=
      fun i => if i = 0 then 0 else if i = 1 then 3 / 4 else 1 / 2
    let localCharge : ℚ := ∑ i : Fin 3, p i * r i
    let targetVariance : ℚ := 11 / 16
    p 0 = 0 ∧ p 1 = 1 / 2 ∧ p 2 = 1 / 2 ∧
      r 0 = 0 ∧ r 1 = 3 / 4 ∧ r 2 = 1 / 2 ∧
      localCharge = 5 / 8 ∧ targetVariance = 11 / 16 ∧
      targetVariance - localCharge = 1 / 16 ∧ localCharge < targetVariance := by
  dsimp
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [Fin.sum_univ_succ, h21]

end MathlibPlus.Combinatorics.Claim48010
