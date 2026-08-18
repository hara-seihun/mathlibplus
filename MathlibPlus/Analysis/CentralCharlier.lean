import Mathlib

/-!
# Central Charlier differential-operator flag

The polynomial family is defined directly by the differential operator from
admitted claim 95.  No recurrence-local replacement is introduced here.
-/

namespace MathlibPlus.Analysis.CentralCharlier

/-- The Euler differential operator `theta = q d/dq`. -/
noncomputable def theta (f : ℝ → ℝ) (q : ℝ) : ℝ :=
  q * deriv f q

/-- The shifted operator `a + theta`, with the fixed parameter `a = 5/4`. -/
noncomputable def shiftedOperator (f : ℝ → ℝ) (q : ℝ) : ℝ :=
  (5 / 4 : ℝ) * f q + theta f q

/-- `P_k(q) = exp(q) (5/4 + theta)^k exp(-q)`. -/
noncomputable def polynomial (k : ℕ) (q : ℝ) : ℝ :=
  Real.exp q * ((shiftedOperator^[k]) (fun x : ℝ => Real.exp (-x))) q

end MathlibPlus.Analysis.CentralCharlier
