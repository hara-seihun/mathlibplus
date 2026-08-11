import Mathlib

/-!
# Endpoint-flat source contract

The admitted claim describes the exact contract for a source used in the
endpoint-flat construction.  No regularity or integrability hypothesis is
added beyond the displayed conditions.
-/

namespace MathlibPlus.Analysis

/-- Claim 4321: a real even source supported in `[-1, 1]`, with zero integral
and vanishing value at the right endpoint. -/
def endpointFlatSource (p : ℝ → ℝ) : Prop :=
  Function.Even p ∧
    Function.support p ⊆ Set.Icc (-1) 1 ∧
    (∫ x : ℝ, p x) = 0 ∧
    p 1 = 0

end MathlibPlus.Analysis
