import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis.HardyLaguerreStationary

/-- The completion factor used by the two completed counterfeits. -/
def completionFactor (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) *
    Complex.cpow (Real.pi : ℂ) (-s / 2) *
      Complex.Gamma (s / 2)

/-- The line member of the same-height pair on the critical line. -/
def linePolynomial (b t : ℝ) : ℝ :=
  (t ^ 2 - b ^ 2) ^ 2

/-- The off-line member of the same-height pair on the critical line. -/
def offPolynomial (a b t : ℝ) : ℝ :=
  ((t - b) ^ 2 + a ^ 2) * ((t + b) ^ 2 + a ^ 2)

/-- The literal real Hardy amplitude of the line member. -/
def lineHardyAmplitude (ω b : ℝ) (t : ℝ) : ℝ :=
  Real.cos (ω * t) * linePolynomial b t /
    ‖completionFactor ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖

/-- The literal real Hardy amplitude of the off-line member. -/
def offHardyAmplitude (ω a b : ℝ) (t : ℝ) : ℝ :=
  Real.cos (ω * t) * offPolynomial a b t /
    ‖completionFactor ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖

/-- The logarithmic curvature of the common completion-factor modulus. -/
def archimedeanLogCurvature (t : ℝ) : ℝ :=
  deriv (deriv (fun u : ℝ =>
    Real.log ‖completionFactor ((1 / 2 : ℂ) + (u : ℂ) * Complex.I)‖)) t

/-- The second derivative used in the first-Laguerre expression. -/
def secondDerivative (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv f) t

/-- The first-Laguerre expression of a real amplitude. -/
def firstLaguerre (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (deriv f t) ^ 2 - f t * secondDerivative f t

/--
Correct stationary orientation for the literal line and off-line Hardy
amplitudes of the same-height pair.

The source's ``nonzero stationary point'' is retained as `H t ≠ 0` together
with `H' t = 0`.  The threshold uses the source's
`M = -inf G''`, where `G(t) = log ‖C(1/2 + it)‖`.
-/
def claim14160 : Prop :=
  ∀ (ω a b M : ℝ),
    0 < a → a < 1 / 2 → 0 < b →
      M = -sInf (Set.range archimedeanLogCurvature) →
        ω ^ 2 > M + 4 / a ^ 2 →
          (∀ t : ℝ,
            lineHardyAmplitude ω b t ≠ 0 →
              deriv (lineHardyAmplitude ω b) t = 0 →
                -lineHardyAmplitude ω b t *
                      secondDerivative (lineHardyAmplitude ω b) t =
                    (deriv (lineHardyAmplitude ω b) t) ^ 2 -
                      lineHardyAmplitude ω b t *
                        secondDerivative (lineHardyAmplitude ω b) t ∧
                  0 < firstLaguerre (lineHardyAmplitude ω b) t) ∧
          (∀ t : ℝ,
            offHardyAmplitude ω a b t ≠ 0 →
              deriv (offHardyAmplitude ω a b) t = 0 →
                -offHardyAmplitude ω a b t *
                      secondDerivative (offHardyAmplitude ω a b) t =
                    (deriv (offHardyAmplitude ω a b) t) ^ 2 -
                      offHardyAmplitude ω a b t *
                        secondDerivative (offHardyAmplitude ω a b) t ∧
                  0 < firstLaguerre (offHardyAmplitude ω a b) t) ∧
          (∀ t : ℝ,
            IsLocalMax (lineHardyAmplitude ω b) t →
              0 < lineHardyAmplitude ω b t) ∧
          (∀ t : ℝ,
            IsLocalMin (lineHardyAmplitude ω b) t →
              lineHardyAmplitude ω b t < 0) ∧
          (∀ t : ℝ,
            IsLocalMax (offHardyAmplitude ω a b) t →
              0 < offHardyAmplitude ω a b t) ∧
          (∀ t : ℝ,
            IsLocalMin (offHardyAmplitude ω a b) t →
              offHardyAmplitude ω a b t < 0)

end MathlibPlus.Open.Analysis.HardyLaguerreStationary
