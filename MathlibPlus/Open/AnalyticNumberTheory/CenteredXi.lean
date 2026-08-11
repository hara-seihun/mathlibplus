import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory

/-!
# First six centered-xi / theta-Mellin coefficient identities

Statement-fidelity registry node for admitted claim 370.  The completed-theta
kernel and its moments are inlined so this node does not depend on separately
queued definitions.
-/

namespace MathlibPlus.Open.AnalyticNumberTheory.CenteredXi

/-- For each `0 ≤ j ≤ 5`, the direct completed-theta Mellin moment equals
`(2j)!` times the `z^(2j)` coefficient of `ξ(1/2+z)`, represented exactly by
the `(2j)`-th iterated derivative at zero. -/
def firstSixMellinCoefficientIdentity : Prop :=
  let shell (n : ℕ) (u : ℝ) : ℝ :=
    (4 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
      6 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))
  let Φ (u : ℝ) : ℝ := ∑' n : ℕ, shell (n + 1) u
  let moment (j : ℕ) : ℝ :=
    2 * ∫ u in Set.Ioi (0 : ℝ), Φ u * u ^ (2 * j)
  let ξ (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta s
  let centered (z : ℂ) : ℂ := ξ (1 / 2 + z)
  ∀ j : ℕ, j ≤ 5 →
    (moment j : ℂ) = iteratedDeriv (2 * j) centered 0

end MathlibPlus.Open.AnalyticNumberTheory.CenteredXi
