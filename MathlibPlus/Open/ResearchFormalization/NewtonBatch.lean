import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.NewtonBatch

noncomputable section

def vandermonde (x : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n,
    ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
      (x j - x i)

def dividedDifference (g : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n,
    g (x i) / (∏ j ∈ (Finset.univ.erase i), (x i - x j))

def prefixNodes (x : Fin n → ℝ) (i : Fin n) : Fin (i.1 + 1) → ℝ :=
  fun j => x ⟨j.1, by omega⟩

/-- Claim 4830: Newton divided-difference rows remove the Vandermonde. -/
def vandermondeRemovalByNewtonRows : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (g : Fin n → ℝ → ℝ),
    (∀ i j : Fin n, i ≠ j → x i ≠ x j) →
      (Matrix.det (fun i j : Fin n => g j (x i)) /
          vandermonde x =
        Matrix.det (fun i j : Fin n =>
          dividedDifference (g j) (prefixNodes x i))) ∧
      (Matrix.det (fun i j : Fin n => g j (x i)) =
        vandermonde x *
          Matrix.det (fun i j : Fin n =>
            dividedDifference (g j) (prefixNodes x i)))

end
end MathlibPlus.Open.ResearchFormalization.NewtonBatch
