import Mathlib
import MathlibPlus.Open.Analysis.SharpMixedShell

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.FirstNonPositiveRealPoleShellOscillation12489

open MathlibPlus.Open.Analysis

/-- Claim 12489 with the reciprocal coefficient carrier, its finite lower
positive-pole data, and the exact non-positive-real first shell. -/
def firstNonPositiveRealPoleShellOscillation_claim12489 : Prop :=
  ∀ (E : ℂ → ℂ) (e : ℕ → ℝ) (R rho : ℝ)
    (lower : Finset ℝ) (multiplicity : ℝ → ℕ)
    (shell : Finset ℂ),
    E 0 = 1 →
    hasRealTaylorCoefficients E e →
    0 < rho →
    rho < R →
    let H : ℂ → ℂ := fun t => 1 / E (-t)
    MeromorphicOn H (Metric.ball (0 : ℂ) R) →
    (∀ a : ℝ, a ∈ lower →
      0 < a ∧ a < rho ∧ 0 < multiplicity a ∧
        hasComplexPoleOrder H (a : ℂ) (multiplicity a)) →
    shell.Nonempty →
    (∀ beta : ℂ, beta ∈ shell →
      ‖beta‖ = rho ∧
        hasComplexPoleOrder H beta 1 ∧
        ¬ ∃ a : ℝ, 0 < a ∧ beta = (a : ℂ)) →
    (∀ beta : ℂ, beta ∈ shell → star beta ∈ shell) →
    (∀ t : ℂ, ‖t‖ ≤ rho →
      (hasComplexPole H t ↔
        (∃ a : ℝ, a ∈ lower ∧ t = (a : ℂ)) ∨ t ∈ shell)) →
    let q : ℕ := lower.sum multiplicity
    Set.Infinite
        {r : ℕ | 0 < determinantFromRealCoefficients e r (q + 1)} ∧
      Set.Infinite
        {r : ℕ | determinantFromRealCoefficients e r (q + 1) < 0}

end MathlibPlus.Open.Analysis.FirstNonPositiveRealPoleShellOscillation12489
