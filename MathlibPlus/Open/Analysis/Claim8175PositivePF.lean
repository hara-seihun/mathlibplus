import Mathlib

namespace MathlibPlus.Open.Analysis.FormalizationBatch

/-- Claim 8175: the zero-extended integer-indexed coefficient sequence is
finite-order Pólya-frequency when all ordered Toeplitz minors through order
`r` are nonnegative, and positivity means positivity at every nonnegative
index. -/
def claim8175_positiveFiniteOrderPolyaFrequency
    (r : ℕ) (f : ℤ → ℝ) : Prop :=
  (∀ n : ℤ, n < 0 → f n = 0) ∧
    (∀ s : ℕ, 1 ≤ s → s ≤ r →
      ∀ rows cols : Fin s → ℤ,
        StrictMono rows → StrictMono cols →
          0 ≤ Matrix.det (fun i j : Fin s => f (cols j - rows i))) ∧
    (∀ n : ℕ, 0 < f (n : ℤ))

end MathlibPlus.Open.Analysis.FormalizationBatch
