import Mathlib
import MathlibPlus.Open.ResearchFormalization.O0314CompletedPair
import MathlibPlus.Open.ResearchFormalization.O0314LogGradient

namespace MathlibPlus.Open.ResearchFormalization.O0314Relocation

noncomputable section

open MathlibPlus.Open.ResearchFormalization.O0314

/-- The real line factor obtained by restricting the canonical even quartic to
 the imaginary axis. -/
noncomputable def lineFactor (b t : ℝ) : ℝ :=
  (lineQuartic b ((t : ℂ) * Complex.I)).re

/-- The real off-line factor obtained by restricting the canonical conjugate
 pair quartic to the imaginary axis. -/
noncomputable def offFactor (a b t : ℝ) : ℝ :=
  (offQuartic a b ((t : ℂ) * Complex.I)).re

/-- Multiplication of the canonical real Hardy amplitude by the line factor. -/
noncomputable def lineHardyAmplitude (b t : ℝ) : ℝ :=
  realHardyZ t * lineFactor b t

/-- Multiplication of the canonical real Hardy amplitude by the off-line
 factor. -/
noncomputable def offHardyAmplitude (a b t : ℝ) : ℝ :=
  realHardyZ t * offFactor a b t

/-- The real logarithmic derivative of the off-line factor. -/
noncomputable def offLogarithmicDerivative (a b t : ℝ) : ℝ :=
  deriv (offFactor a b) t / offFactor a b t

/-- Claim 15342: the canonical Hardy amplitude records the divisor relocation
 in its logarithmic derivative, with the line pole locations and the globally
 smooth off-line logarithmic derivative retained. -/
def claim15342 : Prop :=
  ∀ a b : ℝ, 0 < a → a < 1 / 2 → 0 < b →
    (∀ t : ℝ,
      lineFactor b t = (b ^ 2 - t ^ 2) ^ 2 ∧
        0 ≤ lineFactor b t) ∧
    (∀ t : ℝ,
      offFactor a b t = (t ^ 2 + a ^ 2 - b ^ 2) ^ 2 + 4 * a ^ 2 * b ^ 2 ∧
        0 < offFactor a b t) ∧
    (∀ t : ℝ,
      realHardyZ t ≠ 0 → lineFactor b t ≠ 0 →
        deriv (lineHardyAmplitude b) t / lineHardyAmplitude b t =
          deriv realHardyZ t / realHardyZ t +
            deriv (lineFactor b) t / lineFactor b t) ∧
    (∀ t : ℝ,
      realHardyZ t ≠ 0 → offFactor a b t ≠ 0 →
        deriv (offHardyAmplitude a b) t /
            offHardyAmplitude a b t =
          deriv realHardyZ t / realHardyZ t +
            deriv (offFactor a b) t / offFactor a b t) ∧
    (∀ t : ℝ, t ^ 2 ≠ b ^ 2 →
      deriv (lineFactor b) t / lineFactor b t =
        4 * t / (t ^ 2 - b ^ 2)) ∧
    ContDiff ℝ ⊤ (offLogarithmicDerivative a b)

end

end MathlibPlus.Open.ResearchFormalization.O0314Relocation
