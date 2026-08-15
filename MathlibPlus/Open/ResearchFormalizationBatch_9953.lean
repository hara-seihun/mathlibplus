import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a0014a312d7fbea2e4a2da353f9ad6

namespace MathlibPlus.Open.ResearchFormalizationBatch_9953

noncomputable section

abbrev Source (a R : ℝ) :=
  {f : ℝ → ℝ // f ∈
    MathlibPlus.Open.ResearchFormalizationBatch_01a0014a312d7fbea2e4a2da353f9ad6.annularZeroMeanSourceClass a R}

def mellinTransform (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), (f x : ℂ) * Complex.cpow (x : ℂ) (s - 1)

def crossMellinCommutator (a R : ℝ) (p q : Source a R) (s : ℂ) : ℂ :=
  mellinTransform p s * mellinTransform q (1 - s) -
    mellinTransform q s * mellinTransform p (1 - s)

private def eulerOperator (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => x * deriv f x + (1 / 2 : ℝ) * f x

def centralEulerOperator (a R : ℝ) (f : Source a R) : ℝ → ℝ :=
  fun x => -eulerOperator (eulerOperator f) x

end

end MathlibPlus.Open.ResearchFormalizationBatch_9953
