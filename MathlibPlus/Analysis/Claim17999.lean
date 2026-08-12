import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace MathlibPlus.Analysis

/-- Claim 17999, with the standard principal representative
`gd ξ = arcsin (tanh ξ)` because Mathlib has no Gudermannian constant. -/
theorem gudermannianIdentities_17999 (ξ : ℝ) :
    let θ := Real.arcsin (Real.tanh ξ)
    Real.sin θ = Real.tanh ξ ∧ Real.cos θ = 1 / Real.cosh ξ := by
  dsimp
  have htanh : -1 ≤ Real.tanh ξ ∧ Real.tanh ξ ≤ 1 := by
    have h := Real.tanh_sq_lt_one ξ
    constructor <;> nlinarith
  constructor
  · exact Real.sin_arcsin htanh.1 htanh.2
  · rw [Real.cos_arcsin]
    have hc : Real.cosh ξ ≠ 0 := ne_of_gt (Real.cosh_pos ξ)
    have hrad : 1 - Real.tanh ξ ^ 2 = (1 / Real.cosh ξ) ^ 2 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      field_simp [hc]
      nlinarith [Real.cosh_sq_sub_sinh_sq ξ]
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr (Real.cosh_pos ξ))]

end MathlibPlus.Analysis
