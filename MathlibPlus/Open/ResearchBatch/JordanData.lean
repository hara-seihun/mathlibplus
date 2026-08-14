import Mathlib

namespace MathlibPlus.Open.ResearchBatch.JordanData

def scalarPencil (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then t else 0

def jordanPencil (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else if i = j then t else 0

def scalar_traces_and_determinants_do_not_determine_jordan_data : Prop :=
  (∀ t : ℂ,
      Matrix.charpoly (scalarPencil t) =
          (Polynomial.X - Polynomial.C t) ^ 2 ∧
      Matrix.charpoly (jordanPencil t) =
          (Polynomial.X - Polynomial.C t) ^ 2 ∧
      Matrix.det (scalarPencil t) = Matrix.det (jordanPencil t) ∧
      ∀ k : ℕ, 0 < k →
        Matrix.trace ((scalarPencil t) ^ k) =
          Matrix.trace ((jordanPencil t) ^ k)) ∧
  (∀ x : Fin 2 → ℂ, Matrix.mulVec (scalarPencil 0) x = 0) ∧
  (∀ x : Fin 2 → ℂ,
    Matrix.mulVec (jordanPencil 0) x = 0 ↔ x 1 = 0) ∧
  jordanPencil 0 ≠ 0 ∧
  (jordanPencil 0) ^ 2 = 0

end MathlibPlus.Open.ResearchBatch.JordanData
