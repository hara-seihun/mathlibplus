import Mathlib

/-!
# Coefficient monotonicity for an Axler-type prime-counting majorant

The coefficient derivative, strict coefficient comparison, and pointwise
handoff are stated on the exact positive-denominator carrier from C-0088.
The displayed numerical prime-counting half-lines are not silently added.
-/

namespace MathlibPlus.PrimeCounting

/-- The derivative with respect to the coefficient in the Axler-type majorant. -/
theorem hasDerivAt_axlerRhs_coefficient
    {x c : ℝ} (hx : 1 < x)
    (hden : Real.log x - 1 - c / Real.log x ≠ 0) :
    HasDerivAt (fun a : ℝ => x / (Real.log x - 1 - a / Real.log x))
      ((x / Real.log x) / (Real.log x - 1 - c / Real.log x) ^ 2) c := by
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  convert (hasDerivAt_const c x).div
      ((hasDerivAt_const c (Real.log x - 1)).sub
        ((hasDerivAt_id c).div_const (Real.log x))) hden using 1 <;> try rfl
  dsimp only [Pi.sub_apply, Pi.div_apply, id_eq]
  ring

/-- On the positive-denominator domain, the coefficient derivative is strictly
positive. -/
theorem axlerRhs_coefficient_deriv_pos
    {x c : ℝ} (hx : 1 < x)
    (hden : 0 < Real.log x - 1 - c / Real.log x) :
    0 < deriv (fun a : ℝ => x / (Real.log x - 1 - a / Real.log x)) c := by
  rw [(hasDerivAt_axlerRhs_coefficient hx (ne_of_gt hden)).deriv]
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  exact div_pos (div_pos hxpos hlog) (sq_pos_of_pos hden)

/-- Increasing the coefficient strictly increases the Axler right-hand side
while the larger coefficient's denominator remains positive. -/
theorem axlerRhs_strictMono_coefficient
    {x c₁ c₂ : ℝ} (hx : 1 < x) (hc : c₁ < c₂)
    (hden₂ : 0 < Real.log x - 1 - c₂ / Real.log x) :
    x / (Real.log x - 1 - c₁ / Real.log x) <
      x / (Real.log x - 1 - c₂ / Real.log x) := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hcoeffDiv : c₁ / Real.log x < c₂ / Real.log x :=
    (div_lt_div_iff_of_pos_right hlog).2 hc
  have hdenOrder :
      Real.log x - 1 - c₂ / Real.log x <
        Real.log x - 1 - c₁ / Real.log x := by
    linarith
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  exact div_lt_div_of_pos_left hxpos hden₂ hdenOrder

/-- A strict pointwise bound proved with a smaller coefficient transfers to a
larger coefficient under the same positive-denominator condition. -/
theorem axlerBound_handoff
    {primeCount x c₁ c₂ : ℝ} (hx : 1 < x) (hc : c₁ < c₂)
    (hden₂ : 0 < Real.log x - 1 - c₂ / Real.log x)
    (hbound : primeCount < x / (Real.log x - 1 - c₁ / Real.log x)) :
    primeCount < x / (Real.log x - 1 - c₂ / Real.log x) :=
  hbound.trans (axlerRhs_strictMono_coefficient hx hc hden₂)

end MathlibPlus.PrimeCounting
