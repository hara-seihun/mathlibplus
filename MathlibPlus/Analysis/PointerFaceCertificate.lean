import Mathlib.Tactic

namespace MathlibPlus.Analysis.PointerFaceCertificate

/-- The numerical certificate in admitted claim 46331. -/
theorem numeric_defects
    (D M V : ℚ)
    (hD : D = 5) (hM : M = 19 / 4) (hV : V = 37 / 64) :
    V + 2 * M - 2 * D = 5 / 64 ∧
      0 < V + 2 * M - 2 * D ∧
      V + M - D = 21 / 64 ∧
      ¬ V + M ≤ D := by
  subst D
  subst M
  subst V
  norm_num

end MathlibPlus.Analysis.PointerFaceCertificate
