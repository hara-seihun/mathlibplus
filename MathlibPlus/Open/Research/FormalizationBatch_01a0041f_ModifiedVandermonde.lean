import Mathlib

namespace MathlibPlus.Open.Research

open scoped BigOperators

noncomputable section

def modifiedVandermonde (k : ℕ) (x : Fin k → ℝ) (α : ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j =>
    if i.1 + 1 = k then
      (x j) ^ k / (1 + α * x j)
    else
      (x j) ^ (i.1 + 1)

def finiteVandermonde (k : ℕ) (x : Fin k → ℝ) : ℝ :=
  Finset.prod Finset.univ (fun i =>
    Finset.prod (Finset.univ.filter (fun j => i < j)) (fun j => x j - x i))

/-- The modified Vandermonde determinant identity. -/
def claim_8115 : Prop :=
  ∀ k : ℕ, 0 < k →
    ∀ (x : Fin k → ℝ) (α : ℝ),
      (∀ i, x i ≠ 0) →
      (∀ i j, i ≠ j → x i ≠ x j) →
      (∀ i, 1 + α * x i ≠ 0) →
      Matrix.det (modifiedVandermonde k x α) =
        ((∏ j : Fin k, x j) * finiteVandermonde k x) /
          (∏ j : Fin k, (1 + α * x j)) /\
      Matrix.det (modifiedVandermonde k x α) ≠ 0

end
end MathlibPlus.Open.Research
