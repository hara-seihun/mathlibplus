import Mathlib

/-!
# Third-jet Plücker coordinates

This file gives the exact finite-functional coordinate from admitted claim 60.
The packet does not specify a quantitative meaning for a family being "controlled"
in this quotient, so it does not yet determine a non-vacuous jet-field predicate.
-/

namespace MathlibPlus.ThirdJet

/-- The third forward difference `Δ³ f`. -/
def thirdForwardDifference (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  f (k + 3) - 3 * f (k + 2) + 3 * f (k + 1) - f k

/-- A finite linear functional represented by its finitely supported weights. -/
def applyFiniteFunctional (weights : ℕ →₀ ℝ) (f : ℕ → ℝ) : ℝ :=
  weights.sum fun k weight => weight * f k

/-- The third-jet Plücker coordinate
`[f]_(3,n,j) = f_(n-1) + Q_(n,j)(Δ³ f)`.

The proof `hn` preserves the source's implicit positive-rank domain rather than
silently interpreting `n - 1` at rank zero. -/
def thirdJetPlueckerCoordinate
    (Q : ℕ → ℕ → (ℕ →₀ ℝ)) (f : ℕ → ℝ) (n j : ℕ) (_hn : 1 ≤ n) : ℝ :=
  f (n - 1) + applyFiniteFunctional (Q n j) (thirdForwardDifference f)

end MathlibPlus.ThirdJet
