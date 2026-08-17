import MathlibPlus.Open.Analysis.ResearchFormalizationR0195

namespace MathlibPlus.Open.Analysis.ResearchFormalizationR0195

/-- Claim 18713: the explicit polynomial from Claim 18712 has a largest
positive real root in the certified rational interval. -/
def claim18713_certifiedInterval : Prop :=
  let F : ℝ → ℝ := primitiveRankFourPolynomial
  ∃ ρ₄ : ℝ,
    F ρ₄ = 0 ∧
      0 < ρ₄ ∧
        (∀ x : ℝ, 0 < x → F x = 0 → x ≤ ρ₄) ∧
          (372085690931 : ℝ) / 200000000000 < ρ₄ ∧
            ρ₄ < (7267298651 : ℝ) / 3906250000

end MathlibPlus.Open.Analysis.ResearchFormalizationR0195
