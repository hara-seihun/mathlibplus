import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The exact directed numerical enclosures for the two lower-comparator crossover points. -/
def directedCrossoverEnclosures : Prop :=
  let γ : ℝ := Real.eulerMascheroniConstant
  let Δ : ℝ := γ ^ 2 - 4 * γ + 2
  let sMinus : ℝ := 2 - γ - Real.sqrt Δ
  let sPlus : ℝ := 2 - γ + Real.sqrt Δ
  (1.2668508101540 < sMinus ∧ sMinus < 1.2668508101541) ∧
    (1.5787178600428 < sPlus ∧ sPlus < 1.5787178600429)

end MathlibPlus.Open.ResearchFormalizationBatch
