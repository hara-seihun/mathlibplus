import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchBatchCofactors

def complexifyMatrix {N : ℕ}
    (J : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (J i j : ℂ)

def leadingPrincipalBlock {N : ℕ} (hN : 2 ≤ N)
    (J : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin (N - 1)) (Fin (N - 1)) ℝ :=
  fun i j => J ⟨i.val, by omega⟩ ⟨j.val, by omega⟩

def trailingPrincipalBlock {N : ℕ} (hN : 2 ≤ N)
    (J : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin (N - 1)) (Fin (N - 1)) ℝ :=
  fun i j => J ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩

def complexCharacteristicPolynomial {N : ℕ}
    (J : Matrix (Fin N) (Fin N) ℝ) : Polynomial ℂ :=
  Matrix.charpoly (complexifyMatrix J)

def endpointResolventEntry {N : ℕ}
    (J : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i : Fin N) : ℂ :=
  ((z • (1 : Matrix (Fin N) (Fin N) ℂ) - complexifyMatrix J)⁻¹) i i

/-- The two endpoint resolvents are the corresponding principal cofactors over the characteristic polynomial. -/
def endpointResolventCofactorRatios : Prop :=
  ∀ {N : ℕ} (hN : 2 ≤ N)
    (J : Matrix (Fin N) (Fin N) ℝ) (z : ℂ),
    Polynomial.eval z (complexCharacteristicPolynomial J) ≠ 0 →
      endpointResolventEntry J z ⟨0, by omega⟩ =
          Polynomial.eval z
            (Matrix.charpoly
              (complexifyMatrix (trailingPrincipalBlock hN J))) /
            Polynomial.eval z (complexCharacteristicPolynomial J) ∧
        endpointResolventEntry J z ⟨N - 1, by omega⟩ =
          Polynomial.eval z
            (Matrix.charpoly
              (complexifyMatrix (leadingPrincipalBlock hN J))) /
            Polynomial.eval z (complexCharacteristicPolynomial J)

def realMatrixSpectralRadius {N : ℕ}
    (J : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  sSup
    {r : ℝ |
      ∃ z : ℂ,
        Polynomial.eval z (complexCharacteristicPolynomial J) = 0 ∧
          r = ‖z‖}

/-- One-sided determinant comparison along the forbidden ray. -/
def oneSidedForbiddenRayDeterminantComparison : Prop :=
  ∀ {N : ℕ} (J_L J_R : Matrix (Fin N) (Fin N) ℝ) (x : ℝ),
    (∀ i j, 0 ≤ J_L i j) →
      (∀ i j, 0 ≤ J_R i j) →
        (∀ i j, J_R i j ≤ J_L i j) →
          x > realMatrixSpectralRadius J_L →
            Matrix.det (x • (1 : Matrix (Fin N) (Fin N) ℝ) - J_L) ≤
              Matrix.det (x • (1 : Matrix (Fin N) (Fin N) ℝ) - J_R)

end MathlibPlus.Open.ResearchBatchCofactors
