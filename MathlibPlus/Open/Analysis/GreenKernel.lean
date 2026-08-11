import Mathlib

open MeasureTheory

namespace MathlibPlus.Analysis.GreenKernel

/-- The theta kernel from the preceding coefficient record, before its even
extension.  The `n = 0` term is zero, so the sum over `ℕ` is the same as the
source's sum over `n ≥ 1`. -/
noncomputable def thetaPhiBase (u : ℝ) : ℝ :=
  ∑' n : ℕ,
    (4 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
      6 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))

/-- Even extension of the preceding theta kernel. -/
noncomputable def thetaPhi (u : ℝ) : ℝ := thetaPhiBase |u|

end MathlibPlus.Analysis.GreenKernel

namespace MathlibPlus.Open.Analysis.GreenKernel

open MathlibPlus.Analysis.GreenKernel

/-- Claim 8060.  The integral is over `(x,∞)` and the function `Phi` is the
explicit even theta kernel from the preceding record, not an unconstrained
function parameter. -/
def greenKernelDifferentialEquation : Prop :=
  ∀ (gamma u : ℝ),
    let PhiGamma : ℝ → ℝ := fun x =>
      gamma * ∫ v in Set.Ioi x, thetaPhi v * Real.sin (gamma * (v - x))
    iteratedDeriv 2 PhiGamma u + gamma ^ 2 * PhiGamma u = gamma ^ 2 * thetaPhi u

end MathlibPlus.Open.Analysis.GreenKernel
