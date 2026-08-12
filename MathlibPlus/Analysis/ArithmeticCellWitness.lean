import MathlibPlus.Basic

namespace MathlibPlus.Analysis

/-- The two displayed arithmetic evaluation points lie in consecutive cells. -/
theorem arithmetic_cell_witness_claim13848
    (hpi_lower : (3 : ℝ) < Real.pi) (hpi_upper : Real.pi < 22 / 7) :
    Real.pi < 4 ∧ 4 < 4 * Real.pi ∧
      4 * Real.pi < 13 ∧ 13 < 9 * Real.pi := by
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

end MathlibPlus.Analysis
