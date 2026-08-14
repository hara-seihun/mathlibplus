import Mathlib

namespace MathlibPlus.Open.Analysis.RadauResidue

open scoped BigOperators
open Matrix Finset

noncomputable section

/-- Claim 13036: the modified Radau residue determinant has the displayed
closed form and is nonsingular under the stated node hypotheses. -/
def claim13036 : Prop :=
  ∀ k : ℕ, 0 < k → ∀ (x : Fin k → ℝ) (α : ℝ),
    let M : Matrix (Fin k) (Fin k) ℝ := fun i j =>
      if i.val + 1 = k then
        (x j) ^ k / (1 + α * x j)
      else
        (x j) ^ (i.val + 1)
    let vandermonde : ℝ :=
      (∏ j : Fin k, x j) *
        (∏ i : Fin k, ∏ j : Fin k,
          if i < j then x j - x i else 1)
    M.det = vandermonde / (∏ j : Fin k, (1 + α * x j)) ∧
      (Function.Injective x ∧
        (∀ j : Fin k, x j ≠ 0 ∧ 1 + α * x j ≠ 0) →
        M.det ≠ 0)

end

end MathlibPlus.Open.Analysis.RadauResidue
