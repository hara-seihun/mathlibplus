import Mathlib.NumberTheory.Chebyshev

namespace MathlibPlus.AnalyticNumberTheory.PrimeCounting

/-- The displayed continuous archimedean Lévy density in claim 17549 is
strictly positive on its stated domain. -/
theorem archimedeanLevyDensity_pos_claim17549 (x : ℝ) (hx : 0 < x) :
    0 < Real.exp (-x / 2) / x +
      Real.exp (-5 * x / 2) / (x * (1 - Real.exp (-2 * x))) := by
  have hneg : -2 * x < 0 := by linarith
  have hexp_lt : Real.exp (-2 * x) < 1 := by
    exact (Real.exp_lt_one_iff).2 hneg
  have hden : 0 < x * (1 - Real.exp (-2 * x)) := by
    exact mul_pos hx (sub_pos.mpr hexp_lt)
  exact add_pos (div_pos (Real.exp_pos _) hx)
    (div_pos (Real.exp_pos _) hden)

end MathlibPlus.AnalyticNumberTheory.PrimeCounting
