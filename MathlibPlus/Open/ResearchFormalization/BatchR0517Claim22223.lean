import Mathlib

open scoped BigOperators Matrix

namespace MathlibPlus.Open.ResearchFormalization.BatchR0517Claim22223

private abbrev TransferRing := MvPolynomial (Fin 4) ℤ

private noncomputable def transferMatrix : Matrix (Fin 3) (Fin 3) TransferRing :=
  !![
    MvPolynomial.X 3 * MvPolynomial.X 0, -1,
      -(MvPolynomial.X 1 * MvPolynomial.X 2);
    MvPolynomial.X 3, -1, 0;
    MvPolynomial.X 3, 0, -MvPolynomial.X 2
  ]

private noncomputable def gluingForm : Matrix (Fin 3) (Fin 3) TransferRing :=
  !![
    MvPolynomial.X 3, 0, 0;
    0, -1, 0;
    0, 0, -(MvPolynomial.X 1 * MvPolynomial.X 2)
  ]

/-- Claim 22223: the exact transfer matrix is self-adjoint for the displayed
diagonal gluing form in the source's four-variable polynomial carrier. -/
def claim22223_transferSelfAdjoint : Prop :=
  transferMatrix.transpose * gluingForm =
    gluingForm * transferMatrix

end MathlibPlus.Open.ResearchFormalization.BatchR0517Claim22223
