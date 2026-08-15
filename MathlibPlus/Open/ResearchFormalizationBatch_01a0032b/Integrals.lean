import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Batch_01a0032b

noncomputable section

/-- Claim 8791: the three universal phase integrals. -/
def universalPhaseIntegrals : Prop :=
  (∫ u : ℝ in Set.Ici 0, Real.exp (-u) * Real.arccos (Real.exp (-u)) = 1) ∧
  (∫ u : ℝ in Set.Ici 0,
      Real.exp (-u) * (1 - u) * Real.arccos (Real.exp (-u)) = Real.log 2 - 1) ∧
  (∫ s : ℝ in Set.Ioc 0 1,
      s * Real.log s / Real.sqrt (1 - s ^ 2) = Real.log 2 - 1)

end

end MathlibPlus.Open.Batch_01a0032b
