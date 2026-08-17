import MathlibPlus.Open.LinearAlgebra.OrientedCofactors

namespace MathlibPlus.Open.LinearAlgebra.OrientedCofactors

/-- The `r` by `r+1` row-difference matrix whose successive entries are
`-alpha` and `1`. -/
def rowDifferenceMatrix (r : ℕ) (alpha : ℝ) :
    Matrix (Fin r) (Fin (r + 1)) ℝ :=
  fun i j =>
    if j = Fin.castSucc i then -alpha
    else if j = Fin.succ i then 1
    else 0

/-- The maximal minor left after deleting column `m` from the row-difference
matrix. -/
def rowDifferenceDeletedColumnMinor (r : ℕ) (alpha : ℝ)
    (m : Fin (r + 1)) : ℝ :=
  Matrix.det
    ((rowDifferenceMatrix r alpha).submatrix
      (fun i : Fin r => i) (Fin.succAbove m))

/-- The square matrix obtained by applying the row differences to the
primitive derivative-moment block. -/
noncomputable def rowDifferenceProduct (r k : ℕ) (alpha : ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  rowDifferenceMatrix r alpha * primitiveMatrix r k

/-- Claim 8085: codimension-one Cauchy--Binet for the endpoint row
 differences of the fixed primitive block. -/
def claim8085_codimensionOneCauchyBinetBoundaryFormula : Prop :=
  ∀ (r k : ℕ) (alpha : ℝ),
    let B := primitiveMatrix r k
    let P := rowDifferenceProduct r k alpha
    (∀ m : Fin (r + 1),
      rowDifferenceDeletedColumnMinor r alpha m =
        (-alpha : ℝ) ^ m.val) ∧
      Matrix.det P =
        ∑ m : Fin (r + 1),
          (-alpha : ℝ) ^ m.val * maximalMinor B m

end MathlibPlus.Open.LinearAlgebra.OrientedCofactors
