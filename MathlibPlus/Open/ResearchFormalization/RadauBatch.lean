import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.RadauBatch

noncomputable section

def modifiedRadauMatrix (k : ℕ) (α : ℝ) (x : Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j =>
    if h : i.1 = k - 1 then
      x j ^ k / (1 + α * x j)
    else
      x j ^ (i.1 + 1)

def radauVandermonde (x : Fin k → ℝ) : ℝ :=
  ∏ i : Fin k,
    ∏ j ∈ Finset.univ.filter (fun j : Fin k => i < j),
      (x j - x i)

/-- Claim 13036: the modified Radau residue determinant formula. -/
def modifiedRadauResidueDeterminant : Prop :=
  ∀ (k : ℕ) (α : ℝ) (x : Fin k → ℝ),
    1 ≤ k →
      (∀ i j : Fin k, i ≠ j → x i ≠ x j) →
      (∀ j : Fin k, x j ≠ 0) →
      (∀ j : Fin k, 1 + α * x j ≠ 0) →
      Matrix.det (modifiedRadauMatrix k α x) =
        ((∏ j : Fin k, x j) * radauVandermonde x) /
          (∏ j : Fin k, (1 + α * x j)) ∧
      Matrix.det (modifiedRadauMatrix k α x) ≠ 0

end
end MathlibPlus.Open.ResearchFormalization.RadauBatch
