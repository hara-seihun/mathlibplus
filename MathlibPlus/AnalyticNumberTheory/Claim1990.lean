import Mathlib

namespace MathlibPlus.AnalyticNumberTheory.Claim1990

/-- On the source domain `q ≥ 3`, the corrected parameter makes the two
reciprocal beta bounds identical.  This is the exact algebraic content of the
phrase “the required parameter”; the inequalities alone do not logically
force an equality for an otherwise free parameter. -/
theorem correctedReciprocalParameter
    (q : ℕ) (hq : 3 ≤ q) :
    let qR : ℝ := q
    let c : ℝ := Real.sqrt qR * (Real.log qR) ^ 2 / 100
    1 - 1 / c = 1 - 100 / (Real.sqrt qR * (Real.log qR) ^ 2) := by
  dsimp
  have hqposN : 0 < q := by omega
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqposN
  have hlogpos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hsqrtpos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqpos
  have hdenpos : 0 < Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 :=
    mul_pos hsqrtpos (sq_pos_of_pos hlogpos)
  field_simp [ne_of_gt hdenpos]

end MathlibPlus.AnalyticNumberTheory.Claim1990
