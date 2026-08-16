import MathlibPlus.Open.Analysis.LaguerreFockCritical

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.LaguerreCoefficient15364

noncomputable section

/-- The coefficient expansion of the already named parameter-two generalized
Laguerre carrier. -/
def claim_15364 : Prop :=
  ∀ (d : ℕ) (t : ℝ),
    MathlibPlus.Open.Analysis.LaguerreFockCritical.laguerreTwo d t =
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℝ) ^ k * (Nat.choose (d + 2) (k + 2) : ℝ) * t ^ k /
          (Nat.factorial k : ℝ)

end

end MathlibPlus.Open.NewResearch2.LaguerreCoefficient15364
