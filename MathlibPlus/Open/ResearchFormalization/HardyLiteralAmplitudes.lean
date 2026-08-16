import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Hardy

noncomputable section

/-- The completion factor used by the line/off-line model pair. -/
def completionFactor (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * Complex.cpow (Real.pi : ℂ) (-s / 2) *
    Complex.Gamma (s / 2)

/-- The line member of the same-height model pair. -/
def lineModel (ω b : ℝ) (s : ℂ) : ℂ :=
  Complex.cosh ((ω : ℂ) * (s - (1 / 2 : ℂ))) *
    ((s - (1 / 2 : ℂ)) ^ 2 + (b : ℂ) ^ 2) ^ 2

/-- The off-line member of the same-height model pair. -/
def offModel (ω a b : ℝ) (s : ℂ) : ℂ :=
  Complex.cosh ((ω : ℂ) * (s - (1 / 2 : ℂ))) *
    ((s - (1 / 2 : ℂ)) ^ 2 -
        ((a : ℂ) + Complex.I * (b : ℂ)) ^ 2) *
      ((s - (1 / 2 : ℂ)) ^ 2 -
        ((a : ℂ) - Complex.I * (b : ℂ)) ^ 2)

/-- The quotients of the model pair by the common completion factor. -/
def lineQuotient (ω b : ℝ) (s : ℂ) : ℂ :=
  lineModel ω b s / completionFactor s

def offQuotient (ω a b : ℝ) (s : ℂ) : ℂ :=
  offModel ω a b s / completionFactor s

/-- The real boundary amplitude obtained from a quotient and its common phase. -/
def realHardyAmplitude (F : ℂ → ℂ) (t : ℝ) : ℝ :=
  ((completionFactor ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) /
      (‖completionFactor ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ)) *
      F ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re

/-- Literal Hardy amplitudes of the line/off-line completed pair. -/
def claim_14155 : Prop :=
  ∀ (ω a b : ℝ), 0 < a ∧ a < 1 / 2 ∧ 0 < b →
    (∀ t : ℝ,
      realHardyAmplitude (lineQuotient ω b) t =
        Real.cos (ω * t) * (t ^ 2 - b ^ 2) ^ 2 /
          ‖completionFactor ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖) ∧
      (∀ t : ℝ,
        realHardyAmplitude (offQuotient ω a b) t =
          Real.cos (ω * t) *
              (((t - b) ^ 2 + a ^ 2) * ((t + b) ^ 2 + a ^ 2)) /
            ‖completionFactor ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖)

end

end MathlibPlus.Open.ResearchFormalization.Hardy
