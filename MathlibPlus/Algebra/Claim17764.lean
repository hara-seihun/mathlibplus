import Mathlib

namespace MathlibPlus.Algebra.Claim17764

/-- Claim 17764: evaluation of the affine determinant polynomial gives the
stated determinant of the matrix pencil. -/
def affineDeterminantPolynomialClaim17764
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A B : Matrix n n R) : Prop :=
  ∀ q : R,
    Polynomial.eval q
        (Matrix.det (fun i j =>
          Polynomial.C (B i j) + Polynomial.X * Polynomial.C (A i j))) =
      Matrix.det (B + q • A)

end MathlibPlus.Algebra.Claim17764
