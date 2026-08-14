import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The two-boundary Christoffel matrix with entries `χ`, `ζ`, and `ψ`. -/
def lorentzBoundaryMatrix (χ ζ ψ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![χ, ζ; ζ, ψ]

/-- The Lorentz translate of the determinant of the boundary matrix. -/
def lorentzState (χ ζ ψ : ℝ) : ℝ :=
  χ * (4 - ψ) + ζ ^ 2

/-- The Lorentz quadratic form attached to a boundary state. -/
def lorentzQuadratic (χ ζ ψ a b : ℝ) : ℝ :=
  (4 - ψ) * a ^ 2 - χ * b ^ 2 + 2 * ζ * a * b

/-- The incoming two-port vector. -/
def twoPort (a b : ℝ) : Fin 2 → ℝ :=
  ![a, b]

/-- A positive rank-one update of a two-boundary matrix. -/
def positiveRankOneUpdate
    (MPrev M : Matrix (Fin 2) (Fin 2) ℝ) (p : ℝ) (w : Fin 2 → ℝ) : Prop :=
  0 < p ∧ M = fun i j => MPrev i j + w i * w j / p

/-- Exact Lorentz increment under the positive rank-one Christoffel update. -/
def exactLorentzIncrementFormula : Prop :=
  ∀ (χ ζ ψ p a b : ℕ → ℝ) (n : ℕ),
    0 < n →
    positiveRankOneUpdate
      (lorentzBoundaryMatrix (χ (n - 1)) (ζ (n - 1)) (ψ (n - 1)))
      (lorentzBoundaryMatrix (χ n) (ζ n) (ψ n))
      (p n)
      (twoPort (a n) (b n)) →
    lorentzState (χ n) (ζ n) (ψ n) -
        lorentzState (χ (n - 1)) (ζ (n - 1)) (ψ (n - 1)) =
      lorentzQuadratic (χ (n - 1)) (ζ (n - 1)) (ψ (n - 1)) (a n) (b n) /
        p n

end MathlibPlus.Open.Analysis
