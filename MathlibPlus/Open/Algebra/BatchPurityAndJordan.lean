import Mathlib

noncomputable section
open scoped ComplexConjugate

namespace MathlibPlus.Open.Algebra

def hermitianForm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, conj (v i) * H i j * v j

def PositiveHermitian {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i j, H i j = conj (H j i)) ∧
    (∀ v : Fin n → ℂ, v ≠ 0 → 0 < (hermitianForm H v).re)

def normalizedBySqrt {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (((1 / Real.sqrt q : ℝ) : ℂ) • U)

/-- Claim 12231: a positive Hermitian similitude forces unitary normalization and purity. -/
def positiveSimilitudePurityClaim : Prop :=
  ∀ {n : ℕ} (U H : Matrix (Fin n) (Fin n) ℂ) (q : ℝ),
    0 < q → PositiveHermitian H →
      Matrix.conjTranspose U * H * U = (q : ℂ) • H →
        Matrix.conjTranspose (normalizedBySqrt U q) * H * normalizedBySqrt U q = H ∧
          ∀ (eig : ℂ) (v : Fin n → ℂ), v ≠ 0 → Matrix.mulVec U v = eig • v →
            ‖eig‖ = Real.sqrt q

abbrev polynomialRing := Polynomial ℂ

abbrev polynomialCoker
    (A : Matrix (Fin 2) (Fin 2) polynomialRing) : Type :=
  (Fin 2 → polynomialRing) ⧸
    Submodule.span polynomialRing
      (Set.range (fun v : Fin 2 → polynomialRing => Matrix.mulVec A v))

def diagonalPolynomialMatrix : Matrix (Fin 2) (Fin 2) polynomialRing :=
  !![ Polynomial.X, 0
    ; 0, Polynomial.X ]

def jordanPolynomialMatrix : Matrix (Fin 2) (Fin 2) polynomialRing :=
  !![ Polynomial.X, 1
    ; 0, Polynomial.X ]

def polynomialXIdeal : Ideal polynomialRing :=
  Ideal.span ({Polynomial.X} : Set polynomialRing)

def polynomialXSquaredIdeal : Ideal polynomialRing :=
  Ideal.span ({Polynomial.X ^ 2} : Set polynomialRing)

/-- Claim 12232: equal determinants do not determine the cokernel's Jordan structure. -/
def determinantMultiplicityJordanClaim : Prop :=
  Matrix.det diagonalPolynomialMatrix = Polynomial.X ^ 2 ∧
    Matrix.det jordanPolynomialMatrix = Polynomial.X ^ 2 ∧
    Matrix.det diagonalPolynomialMatrix = Matrix.det jordanPolynomialMatrix ∧
    Nonempty (polynomialCoker diagonalPolynomialMatrix ≃ₗ[polynomialRing]
      (Fin 2 → (polynomialRing ⧸ polynomialXIdeal))) ∧
    Nonempty (polynomialCoker jordanPolynomialMatrix ≃ₗ[polynomialRing]
      (polynomialRing ⧸ polynomialXSquaredIdeal)) ∧
    ¬ Nonempty (polynomialCoker diagonalPolynomialMatrix ≃ₗ[polynomialRing]
      polynomialCoker jordanPolynomialMatrix)

end MathlibPlus.Open.Algebra
