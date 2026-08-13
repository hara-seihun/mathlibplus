import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim57439

/-- The integer inequalities recorded as numerical admissibility for the
surface defect coordinates. -/
def numericallyAdmissible (a d : ℤ) : Prop :=
  0 < a ∧ 0 ≤ d ∧ d ≤ min (9 * a - 1) (7 * a + 6)

/-- The defect coordinate equations recover `K²` and `c₂` from `a` and `d`.
The first hypothesis is the exact-integrality form of
`a = (K² + c₂) / 12`. -/
theorem recover_chern_coordinates
    {a d k c : ℤ}
    (hchi : k + c = 12 * a)
    (hdef : d = 9 * a - k) :
    k = 9 * a - d ∧ c = 3 * a + d := by
  constructor <;> linarith

end MathlibPlus.Algebra.Claim57439
