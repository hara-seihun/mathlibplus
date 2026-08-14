import Mathlib

namespace MathlibPlus.Open

/-- The translated two-boundary Lorentz matrix from the admitted repair context. -/
def lorentzH (χ ζ ψ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![χ, ζ; ζ, ψ - 4]

/-- The Lorentz determinant coordinate `L = -det H`. -/
def lorentzL (χ ζ ψ : ℝ) : ℝ :=
  -Matrix.det (lorentzH χ ζ ψ)

/-- The chosen time-oriented chamber uses both orientation inequalities. -/
def lorentzTimeOriented (χ ζ ψ : ℝ) : Prop :=
  0 < χ ∧ 0 < 4 - ψ

/-- The component opposite to the chosen chamber reverses both orientation signs. -/
def lorentzOppositeTimeComponent (χ ζ ψ : ℝ) : Prop :=
  χ < 0 ∧ 4 - ψ < 0

/--
The Lorentz determinant sign does not orient the cone: positivity of `L = -det H`
alone does not force `ψ < 4`, and states in opposite time components can share
that determinant sign.  The time-oriented chamber therefore retains both
`χ > 0` and `4 - ψ > 0` as orientation data.
-/
def lorentz_determinant_does_not_orient_cone : Prop :=
  (¬ ∀ χ ζ ψ : ℝ, 0 < lorentzL χ ζ ψ → ψ < 4) ∧
    (¬ ∀ χ ζ ψ : ℝ,
      0 < lorentzL χ ζ ψ → lorentzTimeOriented χ ζ ψ) ∧
    (lorentzTimeOriented 1 0 3 ∧
      lorentzOppositeTimeComponent (-1) 0 5 ∧
      0 < lorentzL 1 0 3 ∧
      0 < lorentzL (-1) 0 5)

end MathlibPlus.Open
