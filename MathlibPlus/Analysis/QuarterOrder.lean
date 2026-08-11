import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace MathlibPlus.Analysis.QuarterOrder

/-- Claim 18105: the quarter-order power identity away from the affine zero.
The real powers use Mathlib's totalized `Real.rpow`; the displayed derivative is
therefore asserted only where `1 + q * u ≠ 0`, as in the source. -/
theorem desingularization (q u : ℝ) (hq : q ≠ 0) (h : 1 + q * u ≠ 0) :
    (1 + q * u) ^ (-5 / 4 : ℝ) =
      -(4 / q) * deriv (fun v : ℝ => (1 + q * v) ^ (-1 / 4 : ℝ)) u := by
  have hlin : HasDerivAt (fun v : ℝ => 1 + q * v) q u := by
    have hf : (fun v : ℝ => 1 + q * v) =
        (fun x : ℝ => 1) + (fun y : ℝ => q * y) := by
      funext v
      rfl
    rw [hf]
    simpa using
      ((hasDerivAt_const u (1 : ℝ)).add ((hasDerivAt_id u).const_mul q))
  have hd := (hlin.rpow_const (p := (-1 / 4 : ℝ)) (Or.inl h)).deriv
  rw [hd]
  have hexp : (-1 / 4 : ℝ) - 1 = -5 / 4 := by norm_num
  rw [hexp]
  field_simp [hq]

end MathlibPlus.Analysis.QuarterOrder
