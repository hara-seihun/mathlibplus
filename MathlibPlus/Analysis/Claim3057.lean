import Mathlib

namespace MathlibPlus.Analysis.Claim3057

/-!
The source's positive-sequence context is made explicit by the positivity of
`a₁` and `a₂`; the displayed n = 1 ultra-Turán step is the hypothesis `hT`.
-/

/-- The hard-edge `k = 1` positivity chain. -/
theorem hardEdge_k1_positivity
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {a₀ a₁ a₂ b c₀ : R}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (h₀ : 2 * a₀ > b) (hc₀ : c₀ > a₁)
    (hT : a₁ ^ 2 - b * a₂ > (2 * a₀ - b) * a₂) :
    a₁ * c₀ - b * a₂ > a₁ ^ 2 - b * a₂ ∧
      a₁ ^ 2 - b * a₂ > (2 * a₀ - b) * a₂ ∧
      (2 * a₀ - b) * a₂ > 0 := by
  constructor
  · nlinarith
  constructor
  · exact hT
  · nlinarith

end MathlibPlus.Analysis.Claim3057
