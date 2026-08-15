import Mathlib

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter

namespace MathlibPlus.Open.ResearchFormalization.Batch01a00310.BatchShellConfiguration

def shellVector (r : ℝ) (j : ℕ) : ℝ :=
  r^j / (Nat.factorial (2 * j) : ℝ)

def shellWeight (n : ℕ) : ℝ := Real.rpow (n : ℝ) (-1 / 2 : ℝ)

def shellSupport : Finset ℕ := {4, 16, 25, 64, 144}

def shellRadius (n : ℕ) : ℝ := Real.rpow (n : ℝ) (-2 : ℝ)

def shellMeasure : Measure ℝ :=
  Measure.dirac 1 +
    (1 / 2 : ENNReal) • Measure.dirac (1 / 16 : ℝ) +
    (1 / 4 : ENNReal) • Measure.dirac (1 / 256 : ℝ) +
    (1 / 5 : ENNReal) • Measure.dirac (1 / 625 : ℝ) +
    (1 / 8 : ENNReal) • Measure.dirac (1 / 4096 : ℝ) +
    (1 / 12 : ENNReal) • Measure.dirac (1 / 20736 : ℝ)

end MathlibPlus.Open.ResearchFormalization.Batch01a00310.BatchShellConfiguration
