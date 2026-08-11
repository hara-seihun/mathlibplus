import Mathlib

namespace MathlibPlus.LinearAlgebra.SymplecticLieAlgebra

/--
Claim 4900.  An infinitesimal symplectic relation with respect to a skew form
makes the linearized form symmetric.  The second conjunct records the stated
Cayley normalization as well; the skewness of the ambient form is explicit.
-/
theorem linearizedForm_symmetric
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (J X : Matrix ι ι R)
    (hJ : J.transpose = -J)
    (hX : X.transpose * J + J * X = 0) :
    (J * X).transpose = J * X ∧
      ((1 / 2 : R) • (J * X)).transpose = (1 / 2 : R) • (J * X) := by
  have hX' : X.transpose * J = -(J * X) :=
    eq_neg_of_add_eq_zero_left hX
  have hsymm : (J * X).transpose = J * X := by
    calc
      (J * X).transpose = X.transpose * J.transpose := Matrix.transpose_mul J X
      _ = X.transpose * (-J) := by rw [hJ]
      _ = -(X.transpose * J) := by simp
      _ = -(-(J * X)) := by rw [hX']
      _ = J * X := by simp
  constructor
  · exact hsymm
  · rw [Matrix.transpose_smul, hsymm]

end MathlibPlus.LinearAlgebra.SymplecticLieAlgebra
