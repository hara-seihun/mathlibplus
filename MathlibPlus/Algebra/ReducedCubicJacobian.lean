import Mathlib

namespace MathlibPlus.Algebra.ReducedCubicJacobian

noncomputable section

abbrev Coordinate7152 (K : Type*) := Fin 3 → K
abbrev PolynomialCoordinate7152 (K : Type*) [CommSemiring K] :=
  MvPolynomial (Fin 3) K

/-- The three coordinate polynomials of the reduced cubic map. -/
def reducedCubicComponent7152 {K : Type*} [Field K]
    (i : Fin 3) : PolynomialCoordinate7152 K :=
  let a : PolynomialCoordinate7152 K := MvPolynomial.X 0
  let y : PolynomialCoordinate7152 K := MvPolynomial.X 1
  let z : PolynomialCoordinate7152 K := MvPolynomial.X 2
  ![
    a - MvPolynomial.C (3 / 2 : K) * a ^ 2 * y + a ^ 3 * z,
    MvPolynomial.C (1 / 2 : K) * y - 3 * a * z + 6 * a * y ^ 2 -
        6 * a ^ 2 * y * z + MvPolynomial.C (9 / 2 : K) * a ^ 2 * y ^ 3 -
        3 * a ^ 3 * y ^ 2 * z,
    -2 * z + 4 * y ^ 2 - 6 * a * y * z + 7 * a * y ^ 3 -
        6 * a ^ 2 * y ^ 2 * z + 3 * a ^ 2 * y ^ 4 -
        2 * a ^ 3 * y ^ 3 * z] i

/-- The displayed polynomial map `G` on a coordinate vector. -/
def reducedCubicMap7152 {K : Type*} [Field K]
    (x : Coordinate7152 K) : Coordinate7152 K :=
  let a := x 0
  let y := x 1
  let z := x 2
  ![
    a - (3 / 2 : K) * a ^ 2 * y + a ^ 3 * z,
    (1 / 2 : K) * y - 3 * a * z + 6 * a * y ^ 2 -
        6 * a ^ 2 * y * z + (9 / 2 : K) * a ^ 2 * y ^ 3 -
        3 * a ^ 3 * y ^ 2 * z,
    -2 * z + 4 * y ^ 2 - 6 * a * y * z + 7 * a * y ^ 3 -
        6 * a ^ 2 * y ^ 2 * z + 3 * a ^ 2 * y ^ 4 -
        2 * a ^ 3 * y ^ 3 * z]

/-- The formal partial derivative entry of the Jacobian of `G`. -/
def reducedCubicFormalJacobianEntry7152 {K : Type*} [Field K]
    (x : Coordinate7152 K) (i j : Fin 3) : K :=
  (MvPolynomial.eval x) ((MvPolynomial.pderiv j) (reducedCubicComponent7152 i))

/-- The displayed entrywise Jacobian matrix of the reduced cubic map. -/
def reducedCubicJacobianMatrix7152 {K : Type*} [Field K]
    (x : Coordinate7152 K) : Matrix (Fin 3) (Fin 3) K :=
  let a := x 0
  let y := x 1
  let z := x 2
  !![
    1 - 3 * a * y + 3 * a ^ 2 * z,
      -(3 / 2 : K) * a ^ 2,
      a ^ 3;
    -3 * z + 6 * y ^ 2 - 12 * a * y * z + 9 * a * y ^ 3 -
        9 * a ^ 2 * y ^ 2 * z,
      (1 / 2 : K) + 12 * a * y - 6 * a ^ 2 * z +
        (27 / 2 : K) * a ^ 2 * y ^ 2 - 6 * a ^ 3 * y * z,
      -3 * a - 6 * a ^ 2 * y - 3 * a ^ 3 * y ^ 2;
    -6 * y * z + 7 * y ^ 3 - 12 * a * y ^ 2 * z +
        6 * a * y ^ 4 - 6 * a ^ 2 * y ^ 3 * z,
      8 * y - 6 * a * z + 21 * a * y ^ 2 - 12 * a ^ 2 * y * z +
        12 * a ^ 2 * y ^ 3 - 6 * a ^ 3 * y ^ 2 * z,
      -2 - 6 * a * y - 6 * a ^ 2 * y ^ 2 - 2 * a ^ 3 * y ^ 3]

/-- The reduced map's Jacobian is the displayed matrix, whose determinant is
identically `-1`.  The first conjunct prevents the determinant assertion from
being detached from the derivative of the displayed map. -/
def reducedCubicJacobian_claim7152 : Prop :=
  ∀ (K : Type*) [Field K] [CharZero K] (a y z : K),
    let x : Coordinate7152 K := ![a, y, z]
    (∀ i : Fin 3,
      reducedCubicMap7152 x i =
        (MvPolynomial.eval x) (reducedCubicComponent7152 i)) ∧
    (∀ i j : Fin 3,
      reducedCubicFormalJacobianEntry7152 x i j =
        reducedCubicJacobianMatrix7152 x i j) ∧
      Matrix.det (reducedCubicJacobianMatrix7152 x) = (-1 : K)

end

end MathlibPlus.Algebra.ReducedCubicJacobian
