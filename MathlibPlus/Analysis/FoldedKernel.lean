import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

namespace MathlibPlus.Analysis.FoldedKernel

private theorem foldedKernel_identity_aux (q t : ℝ) :
    Real.exp (-(5 / 4 : ℝ) * t - q * Real.exp (-t)) +
        Real.exp ((5 / 4 : ℝ) * t - q * Real.exp t) =
      2 * Real.exp (-q * Real.cosh t) *
        Real.cosh ((5 / 4 : ℝ) * t - q * Real.sinh t) := by
  simp only [Real.cosh_eq, Real.sinh_eq]
  let C : ℝ := -q * ((Real.exp t + Real.exp (-t)) / 2)
  let A : ℝ := (5 / 4 : ℝ) * t - q * ((Real.exp t - Real.exp (-t)) / 2)
  have hplus : C + A = (5 / 4 : ℝ) * t - q * Real.exp t := by
    dsimp [C, A]
    ring
  have hminus : C + -A = -(5 / 4 : ℝ) * t - q * Real.exp (-t) := by
    dsimp [C, A]
    ring
  change Real.exp (-(5 / 4 : ℝ) * t - q * Real.exp (-t)) +
      Real.exp ((5 / 4 : ℝ) * t - q * Real.exp t) =
    2 * Real.exp C * ((Real.exp A + Real.exp (-A)) / 2)
  symm
  calc
    2 * Real.exp C * ((Real.exp A + Real.exp (-A)) / 2) =
        Real.exp (C + A) + Real.exp (C + -A) := by
          rw [Real.exp_add, Real.exp_add]
          ring
    _ = Real.exp ((5 / 4 : ℝ) * t - q * Real.exp t) +
        Real.exp (-(5 / 4 : ℝ) * t - q * Real.exp (-t)) := by
          rw [hplus, hminus]
    _ = Real.exp (-(5 / 4 : ℝ) * t - q * Real.exp (-t)) +
        Real.exp ((5 / 4 : ℝ) * t - q * Real.exp t) := by ring

/-- Claim 47654: with `q = π x²` and `t = 2u`, the two exponential
expressions agree with the type-B folded-kernel form. -/
theorem foldedKernel_identity_claim47654 (x u : ℝ) :
    let q : ℝ := Real.pi * x ^ 2
    let t : ℝ := 2 * u
    Real.exp (-(5 / 4 : ℝ) * t - q * Real.exp (-t)) +
        Real.exp ((5 / 4 : ℝ) * t - q * Real.exp t) =
      2 * Real.exp (-q * Real.cosh t) *
        Real.cosh ((5 / 4 : ℝ) * t - q * Real.sinh t) := by
  dsimp
  exact foldedKernel_identity_aux (Real.pi * x ^ 2) (2 * u)

end MathlibPlus.Analysis.FoldedKernel
