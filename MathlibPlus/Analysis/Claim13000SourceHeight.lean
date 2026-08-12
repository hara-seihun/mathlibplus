import Mathlib

namespace MathlibPlus.Analysis.Claim13000

/-- The exact source-height arithmetic implication in claim 13000.  The
identities defining `U` and `u` are retained in the interface; the implication
itself only needs the displayed strict inequality. -/
theorem sourceHeightLowerBound
    (α T U u : ℝ) (_hU : U = 2 * T) (_hu : u = Real.log U)
    (hcond : α * (3575 : ℝ) >
      u + Real.log 2 + Real.log (1 + Real.exp (-u))) :
    α > (u + Real.log 2 + Real.log (1 + Real.exp (-u))) / (3575 : ℝ) := by
  have hL : (0 : ℝ) < 3575 := by norm_num
  exact (div_lt_iff₀ hL).2 hcond

end MathlibPlus.Analysis.Claim13000
