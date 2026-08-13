import Mathlib

namespace MathlibPlus.Analysis.Claim17581

/-- The logarithmic derivative of `R` in the coordinate
`τ = (R - 1) / (R + 1)`, with all denominators made explicit. -/
theorem logarithmicRatioDerivative_claim17581
    (R τ : ℝ → ℝ) (x r' τ' : ℝ)
    (hR : HasDerivAt R r' x)
    (hτ : HasDerivAt τ τ' x)
    (hτdef : ∀ z, τ z = (R z - 1) / (R z + 1))
    (hR0 : R x ≠ 0)
    (hplus : R x + 1 ≠ 0)
    (_hden : 1 - τ x ^ 2 ≠ 0) :
    r' / R x = 2 * τ' / (1 - τ x ^ 2) := by
  have hnum : HasDerivAt (fun z => R z - 1) r' x := hR.sub_const 1
  have hdenR : HasDerivAt (fun z => R z + 1) r' x := hR.add_const 1
  have hquot : HasDerivAt (fun z => (R z - 1) / (R z + 1))
      ((r' * (R x + 1) - (R x - 1) * r') / (R x + 1) ^ 2) x := by
    exact hnum.div hdenR hplus
  have hτquot : HasDerivAt (fun z => (R z - 1) / (R z + 1)) τ' x := by
    exact hτ.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z => (hτdef z).symm))
  have hτ'expr : τ' =
      (r' * (R x + 1) - (R x - 1) * r') / (R x + 1) ^ 2 :=
    hτquot.unique hquot
  have hτval : τ x = (R x - 1) / (R x + 1) := hτdef x
  have hτ'simple : τ' = 2 * r' / (R x + 1) ^ 2 := by
    rw [hτ'expr]
    congr 1
    ring
  have hdenexpr :
      1 - ((R x - 1) / (R x + 1)) ^ 2 =
        4 * R x / (R x + 1) ^ 2 := by
    field_simp [hplus]
    ring
  rw [hτval, hτ'simple, hdenexpr]
  field_simp [hR0, hplus]
  ring

end MathlibPlus.Analysis.Claim17581
