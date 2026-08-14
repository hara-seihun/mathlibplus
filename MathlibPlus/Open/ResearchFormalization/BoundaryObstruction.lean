import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The explicit two-edge coefficient-sharing obstruction from claim 40518. -/
def coefficientSharingObstruction40518 : Prop :=
  let uA : ℝ × ℝ := (2, 0)
  let uB : ℝ × ℝ := (0, 2)
  let uC : ℝ × ℝ := (1, 1)
  let boundaryA : ℝ × ℝ := uA - uC
  let boundaryB : ℝ × ℝ := uB - uC
  let μ : Fin 3 → ℕ := fun v =>
    if v = 0 then 2 else if v = 1 then 1 else 0
  (μ 0 > μ 1) ∧
    (μ 1 > μ 2) ∧
    (boundaryA ≠ (0, 0)) ∧
    (boundaryB ≠ (0, 0)) ∧
    (boundaryA + boundaryB = (0, 0))

end MathlibPlus.Open.ResearchFormalization
