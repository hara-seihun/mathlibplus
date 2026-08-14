import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0080

open scoped Classical

noncomputable section

private def diagonalMatrix {n : ℕ} (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then v i else 0

private def absoluteDiagonal {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonalMatrix (fun i => |D i i|)

private def signDiagonal {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonalMatrix (fun i => if 0 ≤ D i i then 1 else -1)

private def inverseSqrtAbsoluteDiagonal {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonalMatrix (fun i => (Real.sqrt |D i i|)⁻¹)

/-- Claim 17759: signed factorization of every finite truncation. -/
def claim17759
    (B L D : ∀ N : ℕ, Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ N : ℕ,
    (∀ i j : Fin N, i ≠ j → D N i j = 0) ∧
      B N = L N * D N * (L N).transpose ∧
      D N = signDiagonal (D N) * absoluteDiagonal (D N)

/-- Claim 17760: the relative operator is the defect from the cluster center
-1, with all inverse and positive-square-root factors explicit. -/
def claim17760
    (A R E L D J Linv LinvT :
      ∀ N : ℕ, Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ N : ℕ,
    Matrix.det (L N) ≠ 0 →
      (∀ i : Fin N, 0 < |D N i i|) →
      Linv N * L N = (1 : Matrix (Fin N) (Fin N) ℝ) ∧
      L N * Linv N = (1 : Matrix (Fin N) (Fin N) ℝ) ∧
      LinvT N * (L N).transpose = (1 : Matrix (Fin N) (Fin N) ℝ) ∧
      (L N).transpose * LinvT N = (1 : Matrix (Fin N) (Fin N) ℝ) ∧
      J N = signDiagonal (D N) ∧
      R N =
        J N * inverseSqrtAbsoluteDiagonal (D N) * Linv N *
          A N * LinvT N * inverseSqrtAbsoluteDiagonal (D N) ∧
      R N = (-1 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ) + E N

end

end MathlibPlus.Open.NewResearch2.R0080
