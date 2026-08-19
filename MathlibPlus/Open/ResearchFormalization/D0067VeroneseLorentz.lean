import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.D0067

noncomputable section

/-- The coordinate realization of the oriented two-dimensional space V. -/
abbrev Plane := Fin 2 → ℝ

/-- The coordinate realization of Sym²(V), with the middle coordinate averaged. -/
abbrev SymSquare := Fin 3 → ℝ

/-- The symplectic area form on V. -/
def symplecticForm (u v : Plane) : ℝ :=
  u 0 * v 1 - u 1 * v 0

/-- The decomposable symmetric tensor `u ⊙ v`. -/
def symSquare (u v : Plane) : SymSquare :=
  ![
    u 0 * v 0,
    (u 0 * v 1 + u 1 * v 0) / 2,
    u 1 * v 1
  ]

/-- The Lorentz bilinear form Q on the symmetric-square coordinates. -/
def lorentzForm (X Y : SymSquare) : ℝ :=
  X 0 * Y 2 + X 2 * Y 0 - 2 * X 1 * Y 1

/-- The associated quadratic form. -/
def quadraticForm (X : SymSquare) : ℝ :=
  lorentzForm X X

/-- The Veronese point `N(u) = u ⊙ u`. -/
def veronese (u : Plane) : SymSquare :=
  symSquare u u

/-- Claim 4924: polarization on decomposable symmetric tensors. -/
def polarizationOnDecomposableSymmetricTensors_claim4924 : Prop :=
  ∀ u v x y : Plane,
    lorentzForm (symSquare u v) (symSquare x y) =
      (symplecticForm u x * symplecticForm v y +
        symplecticForm u y * symplecticForm v x) / 2

/-- Claim 4925: every decomposable symmetric tensor is nonspacelike,
and it is strictly timelike exactly when its symplectic area is nonzero. -/
def decomposableSymmetricTensorNonspacelike_claim4925 : Prop :=
  ∀ u v : Plane,
    quadraticForm (symSquare u v) =
        -(symplecticForm u v) ^ 2 / 2 ∧
      quadraticForm (symSquare u v) ≤ 0 ∧
      (quadraticForm (symSquare u v) < 0 ↔
        symplecticForm u v ≠ 0)

/-- Claim 4926: every Veronese point is null. -/
def veronesePointsAreNull_claim4926 : Prop :=
  ∀ u : Plane, quadraticForm (veronese u) = 0

/-- Claim 4927: pairings of Veronese points are the nonnegative square
of the symplectic pairing. -/
def veronesePointPairingsNonnegative_claim4927 : Prop :=
  ∀ u v : Plane,
    lorentzForm (veronese u) (veronese v) =
        symplecticForm u v ^ 2 ∧
      0 ≤ lorentzForm (veronese u) (veronese v)

end

end MathlibPlus.Open.ResearchFormalization.D0067
