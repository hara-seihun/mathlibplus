import Mathlib

namespace MathlibPlus.Algebra

/-- Claim 8543: the K-0102 Jacobi recurrence has the displayed exact
    discrete-curvature defect. -/
theorem claim8543_discreteCurvature
    (α β c zPrev z zNext : ℝ) (_hc : 0 < c)
    (hrec : zNext = (α / c) * z - (β / c) ^ 2 * zPrev) :
    let ε := α / c - 2
    let ρ := (β / c) ^ 2 - 1
    let F := zNext - 2 * z + zPrev
    F = ε * z - ρ * zPrev := by
  dsimp
  rw [hrec]
  ring

end MathlibPlus.Algebra
