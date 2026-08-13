import MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
import MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting.PriorGlobalCoefficient6098

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-- The coefficient-6097.2 comparison is stronger than the prior coefficient-6098
comparison, since the two majorants differ by a positive multiple of
`x / (log x)^8` on `1 < x`. -/
theorem globalCoefficient6097Point2_implies_priorGlobalCoefficient6098 :
    globalCoefficient6097Point2 → priorGlobalCoefficient6098 := by
  intro h x hx
  have hbound := h x hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hxpos : 0 < x := by linarith
  have hterm : 0 < x / (Real.log x) ^ 8 :=
    div_pos hxpos (pow_pos hlog 8)
  dsimp [globalCoefficient6097Point2, priorGlobalCoefficient6098] at hbound ⊢
  norm_num at hbound ⊢
  let A : ℝ :=
    x / Real.log x + x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 +
      (3012167 / 500000 : ℝ) * x / Real.log x ^ 4 +
      (12012167 / 500000 : ℝ) * x / Real.log x ^ 5 +
      (12012167 / 100000 : ℝ) * x / Real.log x ^ 6 +
      (36036501 / 50000 : ℝ) * x / Real.log x ^ 7
  have hcoeff : (30486 / 5 : ℝ) < 6098 := by norm_num
  have hgap : (30486 / 5 : ℝ) * (x / Real.log x ^ 8) <
      6098 * (x / Real.log x ^ 8) :=
    mul_lt_mul_of_pos_right hcoeff hterm
  calc
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < A + (30486 / 5 : ℝ) * x / Real.log x ^ 8 := by
      simpa [A] using hbound
    _ < A + 6098 * x / Real.log x ^ 8 := by
      convert add_lt_add_left hgap A using 1 <;> ring
    _ = x / Real.log x + x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 +
      (3012167 / 500000 : ℝ) * x / Real.log x ^ 4 +
      (12012167 / 500000 : ℝ) * x / Real.log x ^ 5 +
      (12012167 / 100000 : ℝ) * x / Real.log x ^ 6 +
      (36036501 / 50000 : ℝ) * x / Real.log x ^ 7 +
      6098 * x / Real.log x ^ 8 := by rfl

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
