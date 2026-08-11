import MathlibPlus.Basic

/-!
# Arithmetic consequence of the Noether formula

Claim 14597 supplies the Noether formula and the Chern pair, but does not give
Lean definitions for the surface or its Chern classes.  This file therefore
formalizes the exact numerical implication in `ℚ`; the geometric hypotheses
are represented by the supplied formula and Chern-number equalities.
-/

namespace MathlibPlus.AlgebraicGeometry

/-- The Noether formula with Chern pair `(3, 9)` forces Euler characteristic `1`. -/
theorem noether_eulerCharacteristic_of_chern_pair
    (χ c₁sq c₂ : ℚ)
    (hNoether : χ = (c₁sq + c₂) / 12)
    (hc₁ : c₁sq = 3) (hc₂ : c₂ = 9) :
    χ = 1 := by
  rw [hNoether, hc₁, hc₂]
  norm_num

/-- Claim 14647: the displayed Noether formula and Chern-number values force `χ = 2`.
The source does not identify a Lean surface object, so the numerical formula and
Chern-number equalities are represented directly. -/
theorem noether_eulerCharacteristic_of_chern_pair_5_19
    (χ c₁sq c₂ : ℚ)
    (hNoether : χ = (c₁sq + c₂) / 12)
    (hc₁ : c₁sq = 5) (hc₂ : c₂ = 19) :
    χ = 2 := by
  rw [hNoether, hc₁, hc₂]
  norm_num

end MathlibPlus.AlgebraicGeometry
