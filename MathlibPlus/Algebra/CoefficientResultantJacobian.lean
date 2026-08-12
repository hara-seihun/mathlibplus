import Mathlib

namespace MathlibPlus.Algebra

/--
Claim 7148: for the coefficient--resultant map
`(a,b,c,d,e) ↦ (ac, ad + bc, ae + bd, be, ρ)`, where
`ρ = a^2 e - a b d + c b^2`, the displayed formal Jacobian has
 determinant `-ρ^2`.
-/
theorem fullCoefficientResultantJacobian_claim7148 {R : Type*} [CommRing R]
    (a b c d e : R) :
    let ρ : R := a ^ 2 * e - a * b * d + c * b ^ 2
    Matrix.det
        (!![ c, 0, a, 0, 0;
             d, c, b, a, 0;
             e, d, 0, b, a;
             0, e, 0, 0, b;
             2 * a * e - b * d, 2 * b * c - a * d, b ^ 2, -a * b, a ^ 2 ] :
          Matrix (Fin 5) (Fin 5) R) = -ρ ^ 2 := by
  dsimp
  have detFinFour : ∀ (A : Matrix (Fin 4) (Fin 4) R),
      A.det =
        A 0 0 * (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 -
          A 1 2 * A 2 1 * A 3 3 + A 1 2 * A 2 3 * A 3 1 +
          A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1) -
        A 0 1 * (A 1 0 * A 2 2 * A 3 3 - A 1 0 * A 2 3 * A 3 2 -
          A 1 2 * A 2 0 * A 3 3 + A 1 2 * A 2 3 * A 3 0 +
          A 1 3 * A 2 0 * A 3 2 - A 1 3 * A 2 2 * A 3 0) +
        A 0 2 * (A 1 0 * A 2 1 * A 3 3 - A 1 0 * A 2 3 * A 3 1 -
          A 1 1 * A 2 0 * A 3 3 + A 1 1 * A 2 3 * A 3 0 +
          A 1 3 * A 2 0 * A 3 1 - A 1 3 * A 2 1 * A 3 0) -
        A 0 3 * (A 1 0 * A 2 1 * A 3 2 - A 1 0 * A 2 2 * A 3 1 -
          A 1 1 * A 2 0 * A 3 2 + A 1 1 * A 2 2 * A 3 0 +
          A 1 2 * A 2 0 * A 3 1 - A 1 2 * A 2 1 * A 3 0) := by
    intro A
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
    simp (discharger := decide) [Matrix.det_fin_three, Fin.succAbove]
    ring
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_five]
  simp (discharger := decide) [detFinFour, Fin.succAbove]
  ring

end MathlibPlus.Algebra
