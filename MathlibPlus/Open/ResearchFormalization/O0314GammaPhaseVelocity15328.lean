import MathlibPlus.Open.ResearchFormalization.O0314LogGradient
import MathlibPlus.Open.ResearchFormalization.O0314CompletionCovariance

open Filter

namespace MathlibPlus.Open.ResearchFormalization.O0314GammaPhaseVelocity15328

noncomputable section

/-- The digamma expression for the gamma-side phase velocity. -/
def gammaPhaseVelocity (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).re -
    (1 / 2 : ℝ) * Real.log Real.pi

/-- The outward normal flux on the left half-strip boundary. -/
def leftHalfStripOutwardFlux (t : ℝ) : ℝ :=
  -deriv MathlibPlus.NumberTheory.hardyTheta t

/-- Claim 15328: the canonical completion covariance has the displayed
critical-line logarithmic derivative, the Hardy phase has the exact digamma
velocity and its large-height expansion, and the left-boundary flux is
negative eventually. -/
def claim15328 : Prop :=
  (∀ t : ℝ,
    MathlibPlus.Open.ResearchFormalization.O0314.standardCompletionCovarianceFactor
        (MathlibPlus.Open.ResearchFormalization.O0314.criticalLinePoint t) ≠ 0 →
      deriv
          MathlibPlus.Open.ResearchFormalization.O0314.standardCompletionCovarianceFactor
          (MathlibPlus.Open.ResearchFormalization.O0314.criticalLinePoint t) /
          MathlibPlus.Open.ResearchFormalization.O0314.standardCompletionCovarianceFactor
            (MathlibPlus.Open.ResearchFormalization.O0314.criticalLinePoint t) =
        ((Real.log Real.pi -
            (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I / 2)).re : ℝ) : ℂ)) ∧
    (∀ t : ℝ,
      deriv MathlibPlus.NumberTheory.hardyTheta t = gammaPhaseVelocity t) ∧
    Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ =>
        deriv MathlibPlus.NumberTheory.hardyTheta t -
          (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
      (fun t : ℝ => t⁻¹ ^ 2) ∧
    (∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t →
      leftHalfStripOutwardFlux t < 0)

end

end MathlibPlus.Open.ResearchFormalization.O0314GammaPhaseVelocity15328
