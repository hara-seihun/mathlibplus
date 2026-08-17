import Mathlib
import MathlibPlus.Open.ResearchFormalization.O0314LogGradient
import MathlibPlus.Open.ResearchFormalization.O0314CompletionCovariance

namespace MathlibPlus.Open.ResearchFormalization.O0314

noncomputable section

/-- The canonical functional-equation factor on the critical line. -/
noncomputable def criticalLineChi15326 (t : ℝ) : ℂ :=
  standardCompletionCovarianceFactor (criticalLinePoint t)

/-- Claim 15326: the canonical Hardy phase and real Hardy amplitude give the
critical-line logarithmic derivative, including its real part. -/
def claim15326 : Prop :=
  (∀ t : ℝ, (MathlibPlus.NumberTheory.hardyZ t).im = 0) ∧
    (∀ t : ℝ,
      criticalLineChi15326 t =
          Complex.exp (-2 * Complex.I *
            (MathlibPlus.NumberTheory.hardyTheta t : ℂ)) ∧
        riemannZeta (criticalLinePoint t) =
          Complex.exp (-Complex.I *
            (MathlibPlus.NumberTheory.hardyTheta t : ℂ)) *
            (realHardyZ t : ℂ)) ∧
    (∀ t : ℝ,
      riemannZeta (criticalLinePoint t) ≠ 0 →
        DifferentiableAt ℂ riemannZeta (criticalLinePoint t) ∧
          DifferentiableAt ℝ zetaLogAbs (1 / 2, t) ∧
          riemannZeta (criticalLinePoint t) ≠ 0 ∧
          deriv riemannZeta (criticalLinePoint t) /
              riemannZeta (criticalLinePoint t) =
            (-(deriv MathlibPlus.NumberTheory.hardyTheta t) : ℂ) -
              Complex.I *
                ((deriv realHardyZ t / realHardyZ t : ℝ) : ℂ) ∧
          (deriv riemannZeta (criticalLinePoint t) /
              riemannZeta (criticalLinePoint t)).re =
            -deriv MathlibPlus.NumberTheory.hardyTheta t)

end

end MathlibPlus.Open.ResearchFormalization.O0314
