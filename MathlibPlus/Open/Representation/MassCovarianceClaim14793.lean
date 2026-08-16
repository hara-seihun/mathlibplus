import Mathlib

namespace MathlibPlus.Open.Representation.MassCovarianceClaim14793

noncomputable section

open scoped BigOperators

/-- The two-dimensional mass-whitened class coordinate space. -/
abbrev ClassSpace := Fin 2 → ℂ

/-- The named Eisenstein coefficient `E₁₂`. -/
def E12 : ClassSpace :=
  ![1, 0]

/-- The named cusp coefficient `Δ` before mass whitening. -/
def Delta : ClassSpace :=
  ![0, 1]

/-- The ordered mass-whitened basis `e₀ = E₁₂`, `e₁ = √V_N Δ`. -/
def massBasis (V_N : ℝ) : Fin 2 → ClassSpace :=
  ![E12, (Real.sqrt V_N : ℂ) • Delta]

/-- The bilinear (not Hermitian) mass form in the named `E₁₂, Δ` coordinates. -/
def massBeta (V_N : ℝ) (u v : ClassSpace) : ℂ :=
  u 0 * v 0 + (V_N : ℂ)⁻¹ * u 1 * v 1

/-- Contract the second tensor factor against the mass form.  Thus
`massContraction V u v` is the rank-one coefficient endomorphism
`x ↦ β(v,x) u`. -/
def massContraction (V_N : ℝ) (u v : ClassSpace) : ClassSpace → ClassSpace :=
  fun x => massBeta V_N v x • u

/-- The contraction of the diagonal mass covariance tensor. -/
def diagonalMassContraction (V_N : ℝ) : ClassSpace → ClassSpace :=
  fun x =>
    massContraction V_N (massBasis V_N 0) (massBasis V_N 0) x +
      massContraction V_N (massBasis V_N 1) (massBasis V_N 1) x

/-- Coordinates in the ordered basis `E₁₂, √V_N Δ`. -/
def massCoordinates (V_N : ℝ) (i : Fin 2) (v : ClassSpace) : ℂ :=
  if i = 0 then v 0 else (Real.sqrt V_N : ℂ)⁻¹ * v 1

/-- The coefficient matrix of a coefficient endomorphism in the mass basis. -/
def coefficientMatrix (V_N : ℝ) (F : ClassSpace → ClassSpace) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => massCoordinates V_N i (F (massBasis V_N j))

/--
The diagonal mass covariance of Record 11 is the identity after the exact
mass contraction.  The named `E₁₂` and `√V_N Δ` carriers, the bilinear mass
form, the tensor-to-endomorphism contraction, and its identity coefficient
matrix are all retained explicitly.
-/
def claim14793 : Prop :=
  ∀ (V_N : ℝ),
    0 < V_N →
      (∀ v : ClassSpace,
        ∃ a b : ℂ,
          v = a • massBasis V_N 0 + b • massBasis V_N 1) ∧
      massBeta V_N (massBasis V_N 0) (massBasis V_N 0) = 1 ∧
      massBeta V_N (massBasis V_N 0) (massBasis V_N 1) = 0 ∧
      massBeta V_N (massBasis V_N 1) (massBasis V_N 0) = 0 ∧
      massBeta V_N (massBasis V_N 1) (massBasis V_N 1) = 1 ∧
      (∀ v : ClassSpace,
        diagonalMassContraction V_N v = v) ∧
      coefficientMatrix V_N (diagonalMassContraction V_N) =
        (1 : Matrix (Fin 2) (Fin 2) ℂ)

end

end MathlibPlus.Open.Representation.MassCovarianceClaim14793
