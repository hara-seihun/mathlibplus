import Mathlib

open Filter Set Topology

namespace MathlibPlus.Open.Analysis.FormalizationBatchHardy14158_14159

noncomputable section

/-- The centered variable and the common zeta completion factor. -/
def centered (s : ℂ) : ℂ := s - (1 / 2 : ℂ)

noncomputable def completionFactor (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) *
    Complex.cpow (Real.pi : ℂ) (-s / 2) * Complex.Gamma (s / 2)

noncomputable def criticalPoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * (t : ℂ)

noncomputable def archimedeanLog (t : ℝ) : ℝ :=
  Real.log ‖completionFactor (criticalPoint t)‖

/-- The trigamma function in its defining series. -/
noncomputable def trigamma (z : ℂ) : ℂ :=
  ∑' n : ℕ, (z + (n : ℂ))⁻¹ ^ 2

noncomputable def archimedeanCurvature (t : ℝ) : ℝ :=
  2 * ((1 / 4 : ℝ) - t ^ 2) / (t ^ 2 + 1 / 4) ^ 2 -
    (1 / 4 : ℝ) *
      (trigamma ((1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2)).re

noncomputable def archimedeanM : ℝ :=
  -sInf (Set.range archimedeanCurvature)

noncomputable def offPolynomial (a b t : ℝ) : ℝ :=
  ((t - b) ^ 2 + a ^ 2) * ((t + b) ^ 2 + a ^ 2)

noncomputable def lineHardyAmplitude (ω b t : ℝ) : ℝ :=
  Real.cos (ω * t) * (t ^ 2 - b ^ 2) ^ 2 /
    ‖completionFactor (criticalPoint t)‖

noncomputable def offHardyAmplitude (ω a b t : ℝ) : ℝ :=
  Real.cos (ω * t) * offPolynomial a b t /
    ‖completionFactor (criticalPoint t)‖

noncomputable def realSecondDerivative (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun x : ℝ => deriv f x) t

noncomputable def firstLaguerre (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (deriv f t) ^ 2 - f t * realSecondDerivative f t

noncomputable def logarithmicSecondDerivative (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  realSecondDerivative (fun x : ℝ => Real.log (f x)) t

def criticalCompletionNonzero : Prop :=
  ∀ t : ℝ, completionFactor (criticalPoint t) ≠ 0

/-- The exact off-line first-Laguerre identity and its carrier-zero conclusion. -/
def claim_14158 : Prop :=
  ∀ (a b ω : ℝ),
    0 < a → a < 1 / 2 → 0 < b →
    (∀ t : ℝ, 0 < offPolynomial a b t) ∧
    criticalCompletionNonzero ∧
    (∀ t : ℝ,
      realSecondDerivative archimedeanLog t = archimedeanCurvature t) ∧
    (∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, |archimedeanCurvature t| ≤ B) ∧
    Tendsto archimedeanCurvature atTop (𝓝 0) ∧
    Tendsto archimedeanCurvature atBot (𝓝 0) ∧
    (∀ t : ℝ, -archimedeanM ≤ archimedeanCurvature t) ∧
    (∀ t : ℝ,
      logarithmicSecondDerivative (offPolynomial a b) t ≤ 4 / a ^ 2) ∧
    (∀ t : ℝ, offHardyAmplitude ω a b t ≠ 0 →
      firstLaguerre (offHardyAmplitude ω a b) t /
          offHardyAmplitude ω a b t ^ 2 =
        ω ^ 2 / Real.cos (ω * t) ^ 2 -
          logarithmicSecondDerivative (offPolynomial a b) t +
          realSecondDerivative archimedeanLog t) ∧
    (ω ^ 2 > archimedeanM + 4 / a ^ 2 →
      (∀ t : ℝ, 0 < firstLaguerre (offHardyAmplitude ω a b) t) ∧
      (∀ t : ℝ, offHardyAmplitude ω a b t = 0 →
        0 < (deriv (offHardyAmplitude ω a b) t) ^ 2))

/-- The line member's exact logarithmic curvature and equality at its double zeros. -/
def claim_14159 : Prop :=
  ∀ (a b ω : ℝ),
    0 < a → a < 1 / 2 → 0 < b →
    ω ^ 2 > archimedeanM + 4 / a ^ 2 →
    criticalCompletionNonzero ∧
    (∀ t : ℝ, t ≠ b → t ≠ -b →
      logarithmicSecondDerivative
          (fun x : ℝ => (x ^ 2 - b ^ 2) ^ 2) t =
        -2 / (t - b) ^ 2 - 2 / (t + b) ^ 2) ∧
    (∀ t : ℝ, t ≠ b → t ≠ -b →
      0 < firstLaguerre (lineHardyAmplitude ω b) t) ∧
    (∀ t : ℝ, 0 ≤ firstLaguerre (lineHardyAmplitude ω b) t) ∧
    lineHardyAmplitude ω b b = 0 ∧
    deriv (lineHardyAmplitude ω b) b = 0 ∧
    lineHardyAmplitude ω b (-b) = 0 ∧
    deriv (lineHardyAmplitude ω b) (-b) = 0 ∧
    firstLaguerre (lineHardyAmplitude ω b) b = 0 ∧
    firstLaguerre (lineHardyAmplitude ω b) (-b) = 0

end
end MathlibPlus.Open.Analysis.FormalizationBatchHardy14158_14159
