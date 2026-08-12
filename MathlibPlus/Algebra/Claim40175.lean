import Mathlib

namespace MathlibPlus.Algebra.Claim40175

/-- The numerator in the square-parameter obstruction from claim 40175. -/
def numerator (c : ℤ) : ℤ :=
  8 * c ^ 6 + 9 * c ^ 4 - 8 * c ^ 2 + 3

/-- The displayed numerator is congruent to `3` modulo `c`. -/
theorem numerator_sub_three_dvd_claim40175 (c : ℤ) :
    c ∣ numerator c - 3 := by
  refine ⟨8 * c ^ 5 + 9 * c ^ 3 - 8 * c, ?_⟩
  dsimp [numerator]
  ring

/-- For every integer `c ≥ 2`, the displayed quotient cannot be an integer.
This is the arithmetic obstruction used after the polynomial-square comparison. -/
theorem no_integral_quotient_claim40175 (c : ℤ) (hc : 2 ≤ c) :
    ¬ ∃ q : ℤ, numerator c = (6 * c) * q := by
  rintro ⟨q, hq⟩
  have hdiv : (6 * c) ∣ numerator c := ⟨q, hq⟩
  have hcd : c ∣ numerator c := by
    exact dvd_trans (show c ∣ 6 * c by exact ⟨6, by ring⟩) hdiv
  have hbase : c ∣ 8 * c ^ 6 + 9 * c ^ 4 - 8 * c ^ 2 := by
    refine ⟨8 * c ^ 5 + 9 * c ^ 3 - 8 * c, ?_⟩
    ring
  have hc3 : c ∣ (3 : ℤ) := by
    have hsub := dvd_sub hcd hbase
    have hdiff : numerator c - (8 * c ^ 6 + 9 * c ^ 4 - 8 * c ^ 2) = 3 := by
      dsimp [numerator]
      ring
    rw [hdiff] at hsub
    exact hsub
  have hcle : c ≤ 3 := Int.le_of_dvd (by norm_num) hc3
  have hcpos : 0 < c := by omega
  interval_cases c
  · omega
  · norm_num [numerator] at hdiv

/-- The surviving case `c = 3` has numerator `6492`. -/
theorem numerator_three_claim40175 : numerator 3 = 6492 := by
  norm_num [numerator]

/-- At `c = 3`, divisibility by the full denominator `6c = 18` still fails. -/
theorem three_denominator_obstruction_claim40175 :
    ¬ (18 : ℤ) ∣ numerator 3 := by
  norm_num [numerator]

end MathlibPlus.Algebra.Claim40175
