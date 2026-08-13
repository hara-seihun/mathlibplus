import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim27651

/--
Claim 27651: after choosing a square root `r` of the extra divisor `zeta`,
the two active-axis parameters are the displayed reciprocal pair.  The
source's extra-divisor exclusions are represented explicitly by
`r ≠ 0`, `r ≠ 1`, and `r ≠ -1`; these are exactly the conditions needed for
finiteness, nonzero values, and exclusion of `±1` in this algebraic core.
-/
theorem reciprocalActiveAxisParameters_claim27651
    (zeta r : ℂ) (_hroot : r ^ 2 = zeta)
    (hr0 : r ≠ 0) (hr_one : r ≠ 1) (hr_neg_one : r ≠ -1) :
    let cPlus := -(1 + r) / (1 - r)
    let cMinus := -(1 - r) / (1 + r)
    cPlus * cMinus = 1 ∧
      cPlus ≠ 0 ∧ cMinus ≠ 0 ∧
      cPlus ≠ 1 ∧ cPlus ≠ -1 ∧ cMinus ≠ 1 ∧ cMinus ≠ -1 := by
  dsimp
  have hPlus : (1 + r : ℂ) ≠ 0 := by
    intro h
    apply hr_neg_one
    linear_combination h
  have hMinus : (1 - r : ℂ) ≠ 0 := by
    intro h
    apply hr_one
    exact (sub_eq_zero.mp h).symm
  have hprod :
      (-(1 + r) / (1 - r)) * (-(1 - r) / (1 + r)) = (1 : ℂ) := by
    field_simp [hPlus, hMinus]
  have hcplus0 : -(1 + r) / (1 - r) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hPlus) hMinus
  have hcminus0 : -(1 - r) / (1 + r) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hMinus) hPlus
  have hcplus1 : -(1 + r) / (1 - r) ≠ (1 : ℂ) := by
    intro h
    field_simp [hMinus] at h
    have hbad : (-(1 : ℂ)) = 1 := by
      linear_combination h
    norm_num at hbad
  have hcminus1 : -(1 - r) / (1 + r) ≠ (1 : ℂ) := by
    intro h
    field_simp [hPlus] at h
    have hbad : (-(1 : ℂ)) = 1 := by
      linear_combination h
    norm_num at hbad
  have hcplusneg1 : -(1 + r) / (1 - r) ≠ (-1 : ℂ) := by
    intro h
    field_simp [hMinus] at h
    apply hr0
    linear_combination (-1 / 2 : ℂ) * h
  have hcminusneg1 : -(1 - r) / (1 + r) ≠ (-1 : ℂ) := by
    intro h
    field_simp [hPlus] at h
    apply hr0
    linear_combination (1 / 2 : ℂ) * h
  exact ⟨hprod, hcplus0, hcminus0, hcplus1, hcplusneg1,
    hcminus1, hcminusneg1⟩

end MathlibPlus.Algebra.Claim27651
