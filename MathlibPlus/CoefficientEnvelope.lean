import Mathlib

/-!
# Coefficient-envelope growth

Kernel-checked formalization of the asymptotic scalar implication in Record 8 of
source record `C-0210`.
-/

open Filter

namespace MathlibPlus.CoefficientEnvelope

/-- For a fixed base `r > 1`, any exponent sequence `N / q_N` tending to infinity
forces the corresponding coefficient-envelope lower bound `r ^ (N / q_N)` to tend
to infinity. -/
theorem sublinearOffsetEnvelopeFailure (r : ℝ) (q : ℕ → ℕ) (hr : 1 < r)
    (hq : Tendsto (fun N : ℕ => (N : ℝ) / q N) atTop atTop) :
    Tendsto (fun N : ℕ => r ^ ((N : ℝ) / q N)) atTop atTop :=
  (tendsto_rpow_atTop_of_base_gt_one r hr).comp hq

end MathlibPlus.CoefficientEnvelope
