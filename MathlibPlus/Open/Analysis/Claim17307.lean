import Mathlib

namespace MathlibPlus.Open.Analysis.Claim17307

noncomputable section

/-- The affine vacuum polynomial `P_b(z) = (z + alpha) C(z) - b`. -/
def affineVacuumPolynomial {R : Type*} [CommRing R]
    (C : Polynomial R) (alpha b : R) : Polynomial R :=
  (Polynomial.X + Polynomial.C alpha) * C - Polynomial.C b

/-- Evaluation of the affine vacuum polynomial at a scalar. -/
def affineVacuumPolynomialEval {R : Type*} [CommRing R]
    (C : Polynomial R) (alpha b z : R) : R :=
  (affineVacuumPolynomial C alpha b).eval z

/-- Claim 17307: the displayed polynomial has the stated pointwise affine
form at every scalar. -/
def claim17307 : Prop :=
  ∀ {R : Type*} [CommRing R]
    (C : Polynomial R) (alpha b z : R),
    affineVacuumPolynomialEval C alpha b z =
      (z + alpha) * C.eval z - b

end
end MathlibPlus.Open.Analysis.Claim17307
