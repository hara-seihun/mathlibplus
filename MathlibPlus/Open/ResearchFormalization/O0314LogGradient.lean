import Mathlib
import MathlibPlus.NumberTheory.HardyZ

namespace MathlibPlus.Open.ResearchFormalization.O0314

noncomputable section

open scoped Topology
open Topology

/-- The fixed real Hardy amplitude associated with the canonical Hardy-Z carrier. -/
noncomputable def realHardyZ (t : ℝ) : ℝ :=
  (MathlibPlus.NumberTheory.hardyZ t).re

/-- The critical-line coordinate in the complex plane. -/
noncomputable def criticalLinePoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (t : ℂ) * Complex.I

/-- The logarithmic modulus in the real `(σ,t)` coordinates. -/
noncomputable def zetaLogAbs (p : ℝ × ℝ) : ℝ :=
  Real.log ‖riemannZeta (p.1 + (p.2 : ℂ) * Complex.I)‖

/-- Claim 15327: the fixed zeta/Hardy-Z logarithmic gradient has the
archimedean normal coordinate and the Hardy-amplitude tangential coordinate. -/
def claim15327 : Prop :=
  (∀ t : ℝ, (MathlibPlus.NumberTheory.hardyZ t).im = 0) ∧
    ∀ t : ℝ,
      riemannZeta (criticalLinePoint t) ≠ 0 →
        riemannZeta (criticalLinePoint t) =
          Complex.exp (-((MathlibPlus.NumberTheory.hardyTheta t : ℂ) *
            Complex.I)) * (realHardyZ t : ℂ) ∧
        DifferentiableAt ℝ zetaLogAbs (1 / 2, t) ∧
        (fderiv ℝ zetaLogAbs (1 / 2, t)) (1, 0) =
          -deriv MathlibPlus.NumberTheory.hardyTheta t ∧
        (fderiv ℝ zetaLogAbs (1 / 2, t)) (0, 1) =
          deriv realHardyZ t / realHardyZ t

end

end MathlibPlus.Open.ResearchFormalization.O0314
