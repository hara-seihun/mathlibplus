import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-! The normalization of the de Bruijn--Newman heat family is a source
carrier here; the admitted claim supplies the numerical upper bound but no
canonical Mathlib definition of that normalized Λ. -/

/-- Claim 1035: in the standard Polymath15 normalization, the
De Bruijn--Newman constant is at most `0.186362405`. -/
def deBruijnNewmanUpperBound_claim1035 (Λ : ℝ) : Prop :=
  Λ ≤ (37272481 : ℝ) / 200000000

end MathlibPlus.Open.Analysis
