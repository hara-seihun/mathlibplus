import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.SymplecticCayleyClaim4898

/-- A matrix carrier for a nondegenerate alternating symplectic form.  The
zero diagonal is retained separately from skew-symmetry so the carrier remains
alternating in characteristic two as well. -/
def symplecticForm {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (J : Matrix ι ι R) : Prop :=
  J.transpose = -J ∧
    (∀ i, J i i = 0) ∧
      J.det ≠ 0

/-- Preservation of the displayed symplectic form by a matrix map. -/
def symplecticMap {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (J W : Matrix ι ι R) : Prop :=
  W.transpose * J * W = J

/-- In finite coordinates, `W + I` is invertible when its determinant is a
unit. -/
def cayleyPlusInvertible {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (W : Matrix ι ι R) : Prop :=
  IsUnit ((W + (1 : Matrix ι ι R)).det)

/-- The equivalent absence of the eigenvalue `-1` in the finite-dimensional
coordinate representation. -/
def minusOneNotEigenvalue {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (W : Matrix ι ι R) : Prop :=
  ¬ ∃ v : ι → R, v ≠ 0 ∧ W.mulVec v = (-1 : R) • v

/-- The symplectic Cayley form `J(W-I)(W+I)⁻¹`. -/
noncomputable def symplecticCayleyForm
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (J W : Matrix ι ι R)
    (_hJ : symplecticForm J)
    (_hW : symplecticMap J W)
    (_hPlus : cayleyPlusInvertible W) : Matrix ι ι R :=
  J * (W - (1 : Matrix ι ι R)) *
    (W + (1 : Matrix ι ι R))⁻¹

/-- The admitted symplectic Cayley definition, including the finite-dimensional
`W+I` invertibility/eigenvalue equivalence stated with it. -/
def claim4898 : Prop :=
  ∀ {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (J W : Matrix ι ι R),
    ∀ hJ : symplecticForm J,
      ∀ hW : symplecticMap J W,
        (cayleyPlusInvertible W ↔ minusOneNotEigenvalue W) ∧
          (∀ hPlus : cayleyPlusInvertible W,
            symplecticCayleyForm J W hJ hW hPlus =
              J * (W - (1 : Matrix ι ι R)) *
                (W + (1 : Matrix ι ι R))⁻¹)

end MathlibPlus.Open.LinearAlgebra.SymplecticCayleyClaim4898
