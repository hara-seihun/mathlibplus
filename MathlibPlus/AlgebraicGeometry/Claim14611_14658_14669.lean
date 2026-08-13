import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

namespace MathlibPlus.AlgebraicGeometry

/-- Arithmetic consequence of the displayed Noether data for claim 14611.
The surface and Chern-number interfaces are left as the explicit hypotheses;
no geometric object is invented. -/
theorem noetherEulerValue_claim14611
    (χ c₁sq c₂ : ℚ)
    (hc₁ : c₁sq = 5) (hc₂ : c₂ = 7)
    (hχ : χ = (c₁sq + c₂) / 12) :
    χ = 1 := by
  rw [hχ, hc₁, hc₂]
  norm_num

/-- Arithmetic consequence of the displayed Noether data for claim 14658. -/
theorem noetherEulerValue_claim14658
    (χ c₁sq c₂ : ℚ)
    (hc₁ : c₁sq = 7) (hc₂ : c₂ = 17)
    (hχ : χ = (c₁sq + c₂) / 12) :
    χ = 2 := by
  rw [hχ, hc₁, hc₂]
  norm_num

/-- Arithmetic consequence of the displayed Noether data for claim 14669. -/
theorem noetherEulerValue_claim14669
    (χ c₁sq c₂ : ℚ)
    (hc₁ : c₁sq = 11) (hc₂ : c₂ = 13)
    (hχ : χ = (c₁sq + c₂) / 12) :
    χ = 2 := by
  rw [hχ, hc₁, hc₂]
  norm_num

/-- The explicit divisibility consequence also displayed in claim 14669. -/
theorem noetherEulerDivisibility_claim14669 :
    (12 : ℤ) ∣ (11 + 13) := by
  norm_num

end MathlibPlus.AlgebraicGeometry
