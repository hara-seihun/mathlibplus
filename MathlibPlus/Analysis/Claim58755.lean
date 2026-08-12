import Mathlib.Tactic

namespace MathlibPlus.Analysis

/-- The numerical candidate-rejection consequence in admitted claim 58755.
The Mahler-measure quantities are represented by their real values; the packet's
separate report that no replacement polynomial was supplied is not a theorem. -/
theorem candidateRejectionFromBounds_claim58755 (MC ML : ℝ)
    (hC : (3829 : ℝ) / 1000 < MC) (hL : ML < (19 : ℝ) / 16) :
    MC > ML ∧ ¬ (1 < MC ∧ MC < ML) := by
  constructor
  · linarith
  · intro h
    linarith

end MathlibPlus.Analysis
