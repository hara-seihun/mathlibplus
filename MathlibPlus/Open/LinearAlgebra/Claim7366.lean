import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.Claim7366

def positiveMaximalMinorsAlternatingCoefficients_claim7366 : Prop :=
  ∀ (n : ℕ) (R : Matrix (Fin n) (Fin (n + 1)) ℝ),
    let Δ : Fin (n + 1) → ℝ :=
      fun j => Matrix.det (R.submatrix (fun i => i) (Fin.succAbove j))
    let q : Fin (n + 1) → ℝ :=
      fun j => (-1 : ℝ) ^ (n - j.1) * Δ j / Δ (Fin.last n)
    (Matrix.rank R = n) →
    (Δ (Fin.last n) ≠ 0) →
    (∀ j, 0 < Δ j) →
      (∀ j : Fin n, (-1 : ℝ) ^ (n - j.1) * q (Fin.castSucc j) > 0) ∧
      q (Fin.last n) = 1

end MathlibPlus.Open.LinearAlgebra.Claim7366
