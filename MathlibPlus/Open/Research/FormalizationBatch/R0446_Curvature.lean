import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

open scoped Interval

noncomputable section

/-- The second derivative of the logarithmic current modulus. -/
def logCurrentCurvature (J : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv (fun z : ℝ => Real.log |J z|)) x

def oneSignOnInterval (J : ℝ → ℝ) (a b : ℝ) : Prop :=
  (∀ x ∈ Set.Icc a b, 0 < J x) ∨
    (∀ x ∈ Set.Icc a b, J x < 0)

/-- Exact integral representation of the pressure from logarithmic-current curvature. -/
def exactIntegralOfLogarithmicCurrentCurvature : Prop :=
  ∀ (J : ℝ → ℝ) (a b P : ℝ),
    a < b →
    ContDiff ℝ 2 J →
    oneSignOnInterval J a b →
    P = (b - a) / 2 *
      (deriv J b / J b - deriv J a / J a) →
      P = (b - a) / 2 *
        (∫ x in a..b, logCurrentCurvature J x)

/-- The curvature supremum gives the sufficient pressure budget. -/
def curvatureSupremumGivesPressureBound : Prop :=
  ∀ (J : ℝ → ℝ) (a b P K : ℝ),
    a < b →
    ContDiff ℝ 2 J →
    oneSignOnInterval J a b →
    (∀ x ∈ Set.Icc a b, logCurrentCurvature J x ≤ K) →
    P = (b - a) / 2 *
      (deriv J b / J b - deriv J a / J a) →
      P ≤ K * (b - a) ^ 2 / 2

/-- The same integral representation with the interval-wide sign hypothesis. -/
def curvatureRepresentationUnderIntervalWideSign : Prop :=
  ∀ (J : ℝ → ℝ) (a b P : ℝ),
    a < b →
    ContDiff ℝ 2 J →
    oneSignOnInterval J a b →
    P = (b - a) / 2 *
      (deriv J b / J b - deriv J a / J a) →
      P = (b - a) / 2 *
        (∫ x in a..b, logCurrentCurvature J x)

end

end MathlibPlus.Open.ResearchFormalizationBatch
