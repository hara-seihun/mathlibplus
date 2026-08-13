import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim55175

/-!
Claim 55175 gives an exact replay for the five cases `b = 2, ..., 6`.  The
source spider and U-polynomial carriers are not specified here; the displayed
finite gap table is represented literally and its asserted positivity is
kernel-checked.
-/

/-- The five exact replay gaps, indexed by `b - 2`, in order `b = 2, ..., 6`. -/
def cubicGap : Fin 5 → ℕ := ![426, 4404, 86496, 2138550, 64779018]

/-- Every displayed cubic gap is strictly positive. -/
theorem cubicGaps_positive : ∀ b : Fin 5, 0 < cubicGap b := by
  intro b
  fin_cases b <;> decide

end MathlibPlus.Combinatorics.Claim55175
