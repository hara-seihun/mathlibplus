import MathlibPlus.Open.NumberTheory.Claim9192

namespace MathlibPlus.Open.ResearchFormalization.S0016Claim58978

noncomputable section

open MathlibPlus.Open.NumberTheory.Claim9192

/-- Claim 58978: the smallest Pisot number is characterized exactly as the
unique real root greater than one of the plastic-constant cubic. -/
def claim58978 : Prop :=
  ∃ θ₀ : ℝ,
    θ₀ ^ 3 - θ₀ - 1 = 0 ∧
      1 < θ₀ ∧
      (∀ x : ℝ, x ^ 3 - x - 1 = 0 → x = θ₀) ∧
      PisotNumber θ₀ ∧
      (∀ β : ℝ, PisotNumber β → θ₀ ≤ β)

end

end MathlibPlus.Open.ResearchFormalization.S0016Claim58978
