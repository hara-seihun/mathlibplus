import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.C0095

def bellottiC : ℝ := 87979 / 10000
def bellottiD : ℝ := 13294357 / 100000
def bellottiAStar : ℝ :=
  (bellottiC + 1 + 1 / (10 : ℝ)^80) /
      Real.rpow (108 * Real.log 10) (2 / 3 : ℝ) +
    1.569 * bellottiC * Real.rpow bellottiD (1 / 3 : ℝ)
def bellottiBStar : ℝ := (2 / 9 : ℝ) * Real.sqrt (3 * bellottiD)

def exactBellottiPair_claim1449 : ℝ × ℝ × ℝ × ℝ :=
  (bellottiC, bellottiD, bellottiAStar, bellottiBStar)

def transferredCoefficient : ℝ → ℝ := fun t =>
  (bellottiC + 1 + 1 / (10 : ℝ)^80) /
      Real.rpow (Real.log t) (2 / 3 : ℝ) +
    1.569 * bellottiC * Real.rpow bellottiD (1 / 3 : ℝ)

def transferredCoefficient_claim1451 : Prop :=
  AntitoneOn transferredCoefficient (Set.Ici ((10 : ℝ)^108)) ∧
  transferredCoefficient ((10 : ℝ)^108) = bellottiAStar ∧
  ∀ t : ℝ, t ≥ (10 : ℝ)^108 → transferredCoefficient t ≤ bellottiAStar

def directedNumericalEnclosure_claim1455 : Prop :=
  (70.6994001784669 : ℝ) < bellottiAStar ∧
  bellottiAStar < 70.699401 ∧
  (70.699401 : ℝ) < 70.6995 ∧
  (4.4379436345793 : ℝ) < bellottiBStar ∧
  bellottiBStar < 4.4379437 ∧
  (4.4379437 : ℝ) < 4.43795

end MathlibPlus.Open.ResearchBatch.C0095
