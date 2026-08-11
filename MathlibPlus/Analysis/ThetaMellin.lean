import Mathlib

/-!
# The completed Riemann theta kernel and its factorial moments

Exact source definitions from admitted claim 358.
-/

namespace MathlibPlus.Analysis.ThetaMellin

/-- The `n`th completed-theta shell.  It is zero at `n = 0`; the source
kernel sums the positive-index shells. -/
noncomputable def thetaShell (n : ℕ) (u : ℝ) : ℝ :=
  (4 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
      6 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
    Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))

/-- The completed Riemann theta density on the nonnegative half-line. -/
noncomputable def completedThetaKernel (u : ℝ) : ℝ :=
  ∑' n : ℕ, thetaShell (n + 1) u

/-- The factorial moment indexed by `j`. -/
noncomputable def factorialMoment (j : ℕ) : ℝ :=
  2 * ∫ u in Set.Ici (0 : ℝ), completedThetaKernel u * u ^ (2 * j)

/-- The expanded shell in `completedThetaKernel` has the source's factored
form. -/
theorem thetaShell_eq_factored (n : ℕ) (u : ℝ) :
    thetaShell n u =
      2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) *
        (2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u) - 3) *
          Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)) := by
  have hexp : Real.exp (9 * u / 2) =
      Real.exp (5 * u / 2) * Real.exp (2 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [thetaShell, hexp]
  ring

end MathlibPlus.Analysis.ThetaMellin
