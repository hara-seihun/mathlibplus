import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-!
Claim 15690.  The source's application substitutes `c ^ 2 * x₀` for `base`
and then uses an additional factor `N / x₀`; its sign conditions and the
underlying quantities are not specified there.  This file records the exact
base/scale implication before that contextual application.
-/

/-- Multiplication by a positive scale preserves strict one-step growth from
 a base greater than one. -/
theorem exponentialBaseOneStepGrowth_claim15690
    (base scale : ℝ) (hbase : 1 < base) (hscale : 0 < scale) :
    scale * base < scale * base ^ 2 := by
  have hbase_pos : 0 < base := lt_trans (by norm_num) hbase
  have hstep : base < base ^ 2 := by
    nlinarith
  exact mul_lt_mul_of_pos_left hstep hscale

end MathlibPlus.Algebra
