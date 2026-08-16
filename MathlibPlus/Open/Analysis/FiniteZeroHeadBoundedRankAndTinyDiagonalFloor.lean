import MathlibPlus.Open.ResearchFormalization.Lease01a0014fC5707E67

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- The finite compact Gram heads have rank at most their number of selected
zeros, and their last coordinate has the displayed Rayleigh upper bound. -/
def finiteZeroHeadBoundedRankAndTinyDiagonalFloor : Prop :=
  ∀ (N : ℕ) (x : ℝ) (a : Fin N → ℝ),
    (∀ j : Fin N, x + a j ≠ 0) →
      (∀ k : ℕ,
        let A :=
          MathlibPlus.Open.ResearchFormalization.compactGramMatrix x a (k + 1)
        let i : Fin (k + 1) := Fin.last k
        Matrix.rank A ≤ N ∧
          MathlibPlus.Open.ResearchFormalization.realLeastEigenvalue A ≤ A i i ∧
          A i i =
            2 * ∑ j : Fin N, ((x + a j)⁻¹) ^ (2 * (k + 1))) ∧
      (∃ k : ℕ,
        N < k + 1 ∧
          Matrix.rank
              (MathlibPlus.Open.ResearchFormalization.compactGramMatrix
                x a (k + 1)) < k + 1)

end MathlibPlus.Open.Analysis
