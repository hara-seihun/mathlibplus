import Mathlib

namespace MathlibPlus.Open

noncomputable section

abbrev BatchVec2 := Fin 2 → ℝ

/-- Claim 40370: the differentiated closure at one repaired defect. -/
def claim40370 : Prop :=
  ∀ (A B d : ℝ) (u v : BatchVec2),
    u 0 * v 1 - u 1 * v 0 ≠ 0 →
      (A • u + B • v + d • ((Real.sqrt 2)⁻¹ • (-u + v)) = 0 ↔
        A = d / Real.sqrt 2 ∧ B = -d / Real.sqrt 2)

end

end MathlibPlus.Open
