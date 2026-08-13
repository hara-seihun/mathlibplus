import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim46696

/-- The two exact minimum deterministic-query-cost reports. -/
def selectorAMinCost : ℚ := 2
def selectorBMinCost : ℚ := 2

/-- The saving profiles, indexed by the four Rademacher coordinates. -/
def selectorASaving : Fin 4 → ℚ := ![1, 0, 1 / 2, 1 / 2]
def selectorBSaving : Fin 4 → ℚ := ![0, 1, 1 / 2, 1 / 2]
def averageSaving (i : Fin 4) : ℚ := (selectorASaving i + selectorBSaving i) / 2

theorem selector_minimum_costs :
    selectorAMinCost = 2 ∧ selectorBMinCost = 2 := by
  norm_num [selectorAMinCost, selectorBMinCost]

theorem selector_profiles :
    selectorASaving = ![1, 0, 1 / 2, 1 / 2] ∧
      selectorBSaving = ![0, 1, 1 / 2, 1 / 2] := by
  constructor <;> rfl

theorem averaged_coordinate_saving (i : Fin 4) : averageSaving i = 1 / 2 := by
  fin_cases i <;> norm_num [averageSaving, selectorASaving, selectorBSaving]

end MathlibPlus.Combinatorics.Claim46696
