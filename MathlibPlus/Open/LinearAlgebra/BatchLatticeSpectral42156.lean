import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

open scoped BigOperators
noncomputable section

abbrev LatticeIndex := Fin 7
abbrev LatticeMatrix (R : Type*) [Semiring R] := Matrix LatticeIndex LatticeIndex R

/-- Cast an integral seven-dimensional matrix to a real matrix. -/
def castToReal (A : LatticeMatrix ℤ) : LatticeMatrix ℝ :=
  fun i j => A i j

/-- The integral quadratic form attached to an integral Gram matrix. -/
def integralQuadraticForm (G : LatticeMatrix ℤ) (v : LatticeIndex → ℤ) : ℤ :=
  ∑ i : LatticeIndex, ∑ j : LatticeIndex, v i * G i j * v j

/-- Standard basis vectors in the integral lattice. -/
def standardBasis (i : LatticeIndex) : LatticeIndex → ℤ :=
  fun j => if j = i then 1 else 0

/-- The seven numerical bounds in Record 2. -/
def spectralColumnBounds : LatticeIndex → ℤ :=
  ![8, 12, 12, 16, 8, 8, 8]

/-- The eigenvalue relation for the complexification of an integral matrix. -/
def matrixHasEigenvalue (C : LatticeMatrix ℤ) (eigenvalue : ℂ) : Prop :=
  ∃ v : LatticeIndex → ℂ,
    v ≠ 0 ∧
      (fun i => ∑ j : LatticeIndex, (C i j : ℂ) * v j) = eigenvalue • v

/-- Every eigenvalue lies in the displayed real spectral interval. -/
def spectralWindow (C : LatticeMatrix ℤ) : Prop :=
  ∀ eigenvalue : ℂ, matrixHasEigenvalue C eigenvalue →
    eigenvalue.im = 0 ∧ (-2 : ℝ) < eigenvalue.re ∧
      eigenvalue.re < (2027 : ℝ) / 1000

/-- The hypotheses that make an integral matrix `G`-self-adjoint. -/
def integralGSelfAdjoint (G C : LatticeMatrix ℤ) : Prop :=
  G.transpose = G ∧ G * C = C.transpose * G

/-- Claim 42156: in the seven-dimensional integral Gram setting with the
recorded diagonal, the spectral window gives the displayed quadratic-form
inequality and the seven integral column bounds. -/
def spectralWindowColumnNormBound_claim42156 : Prop :=
  ∀ (G C : LatticeMatrix ℤ),
    (castToReal G).PosDef →
    G.transpose = G →
    integralGSelfAdjoint G C →
    (∀ i : LatticeIndex, G i i = (![2, 3, 3, 4, 2, 2, 2] : LatticeIndex → ℤ) i) →
    spectralWindow C →
    ∀ i : LatticeIndex,
      (integralQuadraticForm G (C.mulVec (standardBasis i)) : ℝ) <
          ((2027 : ℝ) / 1000) ^ 2 *
            (integralQuadraticForm G (standardBasis i) : ℝ) ∧
        integralQuadraticForm G (C.mulVec (standardBasis i)) ≤
          spectralColumnBounds i

/-- The top-left principal submatrix of a real seven-dimensional matrix. -/
def topLeftPrincipal (A : LatticeMatrix ℝ) (r : Fin 8) : Matrix (Fin r.1) (Fin r.1) ℝ :=
  fun i j =>
    A ⟨i.1, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ r.isLt)⟩
      ⟨j.1, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ r.isLt)⟩

/-- The positivity condition on the selected leading principal minors. -/
def leadingPrincipalMinorsPositive (A : LatticeMatrix ℝ) : Prop :=
  ∀ r : Fin 8, 0 < r.1 → 0 < Matrix.det (topLeftPrincipal A r)

/-- Claim 42158: the displayed integral Loewner forms are symmetric, their
positive definiteness is exactly the rational spectral box, and Sylvester's
leading-principal-minor test gives the corresponding exact finite check. -/
def exactLoewnerFormEncoding_claim42158 : Prop :=
  ∀ (G C : LatticeMatrix ℤ),
    (castToReal G).PosDef →
    integralGSelfAdjoint G C →
    let H : LatticeMatrix ℤ :=
      G * (C + (2 : ℤ) • (1 : LatticeMatrix ℤ))
    let J : LatticeMatrix ℤ :=
      (4027 : ℤ) • G - (1000 : ℤ) • H
    H.transpose = H ∧
      J.transpose = J ∧
      ((castToReal H).PosDef ∧ (castToReal J).PosDef ↔ spectralWindow C) ∧
      ((castToReal H).PosDef ↔ leadingPrincipalMinorsPositive (castToReal H)) ∧
      ((castToReal J).PosDef ↔ leadingPrincipalMinorsPositive (castToReal J))

end
end MathlibPlus.Open.LinearAlgebra
