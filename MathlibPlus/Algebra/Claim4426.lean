import Mathlib

namespace MathlibPlus.Algebra.Claim4426

/-- The sign consequences of the normalized-amplitude residue identity in claim 4426.
The packet only asserts the implications on the positive-`α` branch; the ambient
normalization is therefore retained as the explicit equation `c * α = -Res`. -/
theorem normalizedAmplitudeResidueSigns_claim4426
    (α c Res : ℝ) (_hα : α ≠ 0) (hEq : c * α = -Res) :
    α > 0 →
      ((c > 0 ↔ Res < 0) ∧ (c < 0 ↔ Res > 0)) := by
  intro hαpos
  constructor
  · constructor
    · intro hc
      have hprod : 0 < c * α := mul_pos hc hαpos
      linarith
    · intro hres
      by_contra hc
      have hc' : c ≤ 0 := le_of_not_gt hc
      have hprod : c * α ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc' (le_of_lt hαpos)
      linarith
  · constructor
    · intro hc
      have hprod : c * α < 0 := mul_neg_of_neg_of_pos hc hαpos
      linarith
    · intro hres
      by_contra hc
      have hc' : 0 ≤ c := le_of_not_gt hc
      have hprod : 0 ≤ c * α :=
        mul_nonneg hc' (le_of_lt hαpos)
      linarith

end MathlibPlus.Algebra.Claim4426
