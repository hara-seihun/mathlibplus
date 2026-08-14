import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

noncomputable section

/-- The logarithmic carrier data from the exact signed-split repair context. -/
def carrierLogDerivative (A : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv A x / A x

def carrierSecondCoefficient (A : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv (carrierLogDerivative A) x

def carrierPhase (A : ℝ → ℂ) (x : ℝ) : ℂ :=
  A x / (‖A x‖ : ℂ)

def carrierImaginaryDerivative (A : ℝ → ℂ) (x : ℝ) : ℝ :=
  (carrierLogDerivative A x).im

def carrierCurvature (A : ℝ → ℂ) (x : ℝ) : ℝ :=
  2 * carrierImaginaryDerivative A x ^ 2 -
    (carrierSecondCoefficient A x).re

def carrierFirstLaguerre (A G : ℝ → ℂ) (x : ℝ) : ℝ :=
  let p := carrierImaginaryDerivative A x
  let b := carrierSecondCoefficient A x
  let c := carrierCurvature A x
  let w := carrierPhase A x
  c * ‖G x‖ ^ 2 +
      4 * p * (deriv G x * star (G x)).im +
      ‖deriv G x‖ ^ 2 -
      (G x * star (deriv (deriv G) x)).re +
      (w ^ 2 *
        ((deriv G x) ^ 2 - G x * deriv (deriv G) x - b * (G x) ^ 2)).re

def carrierBaseline (A : ℝ → ℂ) (x : ℝ) : ℝ :=
  carrierCurvature A x -
    (carrierPhase A x ^ 2 * carrierSecondCoefficient A x).re

def carrierPZero (A T : ℝ → ℂ) (x : ℝ) : ℂ :=
  -deriv (deriv T) x -
    4 * Complex.I * (carrierImaginaryDerivative A x : ℂ) * deriv T x +
    2 * (carrierCurvature A x : ℂ) * T x

def carrierPOne (A T : ℝ → ℂ) (x : ℝ) : ℂ :=
  -deriv (deriv T) x - 2 * carrierSecondCoefficient A x * T x

/-- Claim 6032: the exact signed carrier split, pointwise on the interval. -/
def claim6032_signedCarrierSplit : Prop :=
  ∀ (I : Set ℝ) (A T : ℝ → ℂ),
    Set.OrdConnected I ∧
      (∀ x : ℝ, x ∈ I → A x ≠ 0) ∧
      ContDiff ℝ 2 A ∧
      ContDiff ℝ 2 T →
    ∀ x : ℝ, x ∈ I →
      carrierFirstLaguerre A (fun y => 1 + T y) x =
        carrierBaseline A x +
          (carrierPZero A T x).re +
          (carrierPhase A x ^ 2 * carrierPOne A T x).re +
          carrierFirstLaguerre A T x

end
end MathlibPlus.Open.FormalizationBatch
