import Mathlib

namespace MathlibPlus.Open.Combinatorics.R0941

open scoped BigOperators
open MvPolynomial

abbrev FourShapePolynomial := MvPolynomial (Fin 4) ℚ

noncomputable def shapeT : FourShapePolynomial := X 0
noncomputable def shapeE : FourShapePolynomial := X 1
noncomputable def shapeF : FourShapePolynomial := X 2
noncomputable def shapeG : FourShapePolynomial := X 3

noncomputable def H4K1 : FourShapePolynomial := 1
noncomputable def HK2plus2K1 : FourShapePolynomial :=
  1 + shapeT * shapeE
noncomputable def HP3plusK1 : FourShapePolynomial :=
  1 + shapeT * (2 * shapeE + shapeF)
noncomputable def H2K2 : FourShapePolynomial :=
  (1 + shapeT * shapeE) ^ 2
noncomputable def HP4 : FourShapePolynomial :=
  1 + shapeT * (3 * shapeE + 2 * shapeF + shapeG) +
    shapeT ^ 2 * shapeE ^ 2
noncomputable def HK13 : FourShapePolynomial :=
  1 + shapeT * (3 * shapeE + 3 * shapeF + shapeG)

/-- The coefficient vectors in the ordered basis
    `(1,te,tf,tg,t^2 e^2)`. -/
noncomputable def fourShapeCoefficientMatrix :
    Matrix (Fin 6) (Fin 5) ℚ :=
  !![1, 0, 0, 0, 0;
     1, 1, 0, 0, 0;
     1, 2, 1, 0, 0;
     1, 2, 0, 0, 1;
     1, 3, 2, 1, 1;
     1, 3, 3, 1, 0]

/-- R-0941.2: all six four-vertex complement forests have the displayed
    normalized series, the coefficient vectors have rank five, and the one
    displayed rectangle is the unique linear relation up to scalar. -/
def r0941_sixFourVertexShapes : Prop :=
  H4K1 = 1 ∧
    HK2plus2K1 = 1 + shapeT * shapeE ∧
    HP3plusK1 = 1 + shapeT * (2 * shapeE + shapeF) ∧
    H2K2 = (1 + shapeT * shapeE) ^ 2 ∧
    HP4 = 1 + shapeT * (3 * shapeE + 2 * shapeF + shapeG) +
      shapeT ^ 2 * shapeE ^ 2 ∧
    HK13 = 1 + shapeT * (3 * shapeE + 3 * shapeF + shapeG) ∧
    Matrix.rank fourShapeCoefficientMatrix = 5 ∧
    H2K2 + HK13 = HP3plusK1 + HP4

end MathlibPlus.Open.Combinatorics.R0941
