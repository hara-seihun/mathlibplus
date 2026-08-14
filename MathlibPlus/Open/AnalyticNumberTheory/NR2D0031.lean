import MathlibPlus.Analysis.ReciprocalXi

noncomputable section

namespace MathlibPlus.Open.AnalyticNumberTheory.NR2D0031

private def xi (s : ℂ) : ℂ := MathlibPlus.Analysis.ReciprocalXi.xi s

private def centeredXi (z : ℂ) : ℂ := xi ((1 / 2 : ℂ) + z)

private def riemannHypothesis : Prop :=
  ∀ s : ℂ, xi s = 0 → s.re = 1 / 2

private def centeredImaginaryZeros : Prop :=
  ∀ z : ℂ, centeredXi z = 0 → z.re = 0

private def realVariableOnlyRealZeros : Prop :=
  ∀ z : ℂ, centeredXi (Complex.I * z) = 0 → z.im = 0

/-- Claim 4638: centered Xi is entire, even, and real on the real axis. -/
def claim4638 : Prop :=
  Differentiable ℂ xi ∧
    (∀ z : ℂ, xi ((1 / 2 : ℂ) + z) = xi ((1 / 2 : ℂ) - z)) ∧
      ∀ x : ℝ, (xi (x : ℂ)).im = 0

/-- Claim 4639: the three centered-coordinate formulations of RH are
logically equivalent. -/
def claim4639 : Prop :=
  (riemannHypothesis ↔ centeredImaginaryZeros) ∧
    (riemannHypothesis ↔ realVariableOnlyRealZeros)

end MathlibPlus.Open.AnalyticNumberTheory.NR2D0031
