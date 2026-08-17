import MathlibPlus.Open.ResearchFormalization.R3720TreeU

namespace MathlibPlus.Open.ResearchFormalization.R3720

noncomputable section

open MathlibPlus.Open.TreeSpectral

/-- The ordered product of `k` successive raising operators beginning at
`researchGamma n`. -/
def gammaIterate : (n k : ℕ) → ResearchPolynomial → ResearchPolynomial
  | n, 0, f => f
  | n, k + 1, f => researchGamma (n + k) (gammaIterate n k f)

/-- Claim 48417: a nonzero first pendant moment in the U-kernel persists
under every iterated all-vertex leaf grafting. -/
def claim_48417 : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ k : ℕ, 1 ≤ k →
      (∀ j : ℕ, j < k → gammaWeightInjective (n - 1 + j)) ∧
      ∀ w : TreeSpace n, w ∈ uKernel n →
        momentMap (n + k) (graftPow n k w) =
          gammaIterate (n - 1) k (momentMap n w)) ∧
    ∀ w : TreeSpace n, w ∈ uKernel n →
      momentMap n w ≠ 0 →
        ∀ k : ℕ,
          momentMap (n + k) (graftPow n k w) ≠ 0

end
end MathlibPlus.Open.ResearchFormalization.R3720
