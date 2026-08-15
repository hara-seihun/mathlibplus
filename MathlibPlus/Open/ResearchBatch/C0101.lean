import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.C0101

def dualCertificatePhi (u : ℝ) : ℝ := 1 + Real.log u - (3 / 2 + Real.log 2) * (u - 1)

def dualCertificateInequalities_claim1558 : Prop :=
  dualCertificatePhi 1 = 1 ∧
  dualCertificatePhi 2 = -(1 / 2 : ℝ) ∧
  (∀ u : ℝ, 1 ≤ u → u ≤ 2 → |dualCertificatePhi u| ≤ 1 / u) ∧
  (∀ u : ℝ, 1 < u → u < 2 → |dualCertificatePhi u| < 1 / u) ∧
  (∀ u : ℝ, 0 < u →
    deriv (fun v : ℝ => 1 / v - dualCertificatePhi v) u =
      (3 / 2 + Real.log 2) - 1 / u - 1 / u^2) ∧
  (∀ u : ℝ, 0 < u →
    deriv (fun v : ℝ => dualCertificatePhi v + 1 / v) u =
      (u - 1) / u^2 - (3 / 2 + Real.log 2)) ∧
  (3 / 2 + Real.log 2) - 2 > 0 ∧
  1 / 4 - (3 / 2 + Real.log 2) < 0 ∧
  (∀ u : ℝ, 1 ≤ u → u ≤ 2 →
    deriv (fun v : ℝ => 1 / v - dualCertificatePhi v) u ≥
      (3 / 2 + Real.log 2) - 2) ∧
  (∀ u : ℝ, 1 ≤ u → u ≤ 2 →
    deriv (fun v : ℝ => dualCertificatePhi v + 1 / v) u ≤
      1 / 4 - (3 / 2 + Real.log 2))

-- The derivative lower and upper bounds are recorded in the claim itself; the
-- following explicit identities are the exact counterexample surface.
def complexMeanValueFunction (T : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((t - T) / T))

def complexMeanValueCounterfeit_claim1563 : Prop :=
  ∀ T : ℝ, 0 < T →
    ContinuousOn (complexMeanValueFunction T) (Set.Icc T (2 * T)) ∧
    ((1 / (T : ℂ)) *
      (∫ t in T..(2 * T), complexMeanValueFunction T t)) = 0 ∧
    (∀ t : ℝ, t ∈ Set.Icc T (2 * T) →
      ‖complexMeanValueFunction T t‖ = 1)

end MathlibPlus.Open.ResearchBatch.C0101
