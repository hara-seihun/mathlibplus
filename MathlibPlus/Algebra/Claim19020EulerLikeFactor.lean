import Mathlib

namespace MathlibPlus.Algebra.Claim19020

/-- The local factor defined in admitted claim 19020.  It is total as a Lean
function; the source domain restrictions `0 < q` and `0 < ell` are hypotheses
for its intended use, not silently folded into the definition. -/
noncomputable def euler_like_factor_claim19020 (q ell z : ℝ) : ℝ :=
  (1 + q * Real.exp (ell * z)) * (1 + q * Real.exp (-(ell * z)))

end MathlibPlus.Algebra.Claim19020
