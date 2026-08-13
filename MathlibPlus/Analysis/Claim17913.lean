import Mathlib.Tactic

namespace MathlibPlus.Analysis.Claim17913

/-- The positive next contiguous minor forced by a Desnanot--Jacobi identity
    and a strict correlation bound. -/
theorem positiveNextOfDesnanotJacobi_claim17913
    (next prev left right ρ : ℝ)
    (hprev : 0 < prev)
    (hleft : 0 < left)
    (hright : 0 < right)
    (hρ : |ρ| < 1)
    (hDJ : next * prev = left * right * (1 - ρ ^ 2)) :
    0 < next := by
  have hρbounds : -1 < ρ ∧ ρ < 1 := (abs_lt.mp hρ)
  have hρsq : ρ ^ 2 < 1 := by
    nlinarith [sq_nonneg (ρ - 1), sq_nonneg (ρ + 1)]
  have hfactor : 0 < 1 - ρ ^ 2 := by linarith
  have hprod : 0 < left * right * (1 - ρ ^ 2) := by positivity
  have hnextprod : 0 < next * prev := by nlinarith [hDJ]
  nlinarith

end MathlibPlus.Analysis.Claim17913
