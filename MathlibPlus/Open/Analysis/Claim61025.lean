import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim61025

noncomputable section

/-- The finite moment sequence associated with the 27 displayed values. -/
def moments (y : Fin 27 → ℝ) (k : ℕ) : ℝ :=
  ∑ a : Fin 27, y a ^ k

/-- The 3-by-3 Hankel matrix from the first five moments. -/
def hankel (y : Fin 27 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => moments y (i.1 + j.1)

/-- At least three distinct values occur in the displayed 27-tuple. -/
def hasThreeDistinctValues (y : Fin 27 → ℝ) : Prop :=
  ∃ a b c : Fin 27,
    y a ≠ y b ∧ y a ≠ y c ∧ y b ≠ y c

/-- The ordered three-point Vandermonde sum. -/
def vandermondeSum (y : Fin 27 → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun a =>
    Finset.sum (Finset.univ.filter (fun b : Fin 27 => a < b)) (fun b =>
      Finset.sum (Finset.univ.filter (fun c : Fin 27 => b < c)) (fun c =>
        (y a - y b) ^ 2 * (y a - y c) ^ 2 * (y b - y c) ^ 2)))

/--
The exact corrected 27-atom Hankel-rank assertion: the moment matrix is
positive semidefinite, its determinant is the three-point Vandermonde sum,
and strict positivity is exactly the presence of three distinct values.
-/
def correctedHankelRankClaim : Prop :=
  (∀ y : Fin 27 → ℝ,
    (∀ a : Fin 27, 0 < y a ∧ y a < 4) →
      Matrix.PosSemidef (hankel y) ∧
        Matrix.det (hankel y) = vandermondeSum y ∧
        (Matrix.PosDef (hankel y) ↔ hasThreeDistinctValues y) ∧
        (0 < Matrix.det (hankel y) ↔ hasThreeDistinctValues y)) ∧
  (∃ y : Fin 27 → ℝ,
    (∀ a : Fin 27, 0 < y a ∧ y a < 4) ∧
      Matrix.PosSemidef (hankel y) ∧
      ¬ Matrix.PosDef (hankel y) ∧
      Matrix.det (hankel y) = 0)

end

end MathlibPlus.Open.Analysis.Claim61025
