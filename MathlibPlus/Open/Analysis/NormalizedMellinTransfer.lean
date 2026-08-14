import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The exact normalized Mellin transfer relation from admitted claim 13366. -/
def normalizedMellinTransferClaim (c : ℂ) (A : ℂ → ℂ) : Prop :=
  c = 1 / riemannZeta (2 : ℂ) ∧
    ∀ s : ℂ,
      A s = ((s - 1) / (c * s)) * riemannZeta s / riemannZeta (s + 1)

end MathlibPlus.Open.Analysis
