import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.C0157

def gaussianHermiteH (x : ℝ) : ℝ :=
  x^2 * (2 * Real.pi * x^2 - 3) * Real.exp (-Real.pi * x^2)
def gaussianHermiteG (x : ℝ) : ℝ := Real.exp (-Real.pi * x^2)
def gaussianHermiteR2 (x : ℝ) : ℝ :=
  x^2 * gaussianHermiteH x - 3 / (2 * Real.pi^2) * gaussianHermiteG x
def gaussianHermiteRperp (x : ℝ) : ℝ :=
  (x^4 - 5 / Real.pi * x^2) * gaussianHermiteH x

def gaussianHermiteDirections_claim2455 :
    (ℝ → ℝ) × (ℝ → ℝ) :=
  (gaussianHermiteR2, gaussianHermiteRperp)

end MathlibPlus.Open.ResearchBatch.C0157
