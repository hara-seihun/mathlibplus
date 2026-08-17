import MathlibPlus.Open.Analysis.WeightedShellWatsonClaims18438_18442

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim18440

noncomputable section

/-- Claim 18440: every admissible alternating Taylor truncation encloses the
normalized weighted-shell moment between its odd and even partial sums. -/
def claim18440 : Prop :=
  ∀ (m j K : ℕ),
    weightedShellTowerAdmissible_claim18442 m j K →
      let a := weightedShellA_claim18438 m
      let ρ := weightedShellRho_claim18438 m
      let ν := weightedShellNu_claim18438 j
      let t := weightedShellMoment_claim18438 m j
      let R := t / (2 * Real.exp (-a) / ρ ^ ν)
      let Sodd := weightedShellTowerSum_claim18440 m j (2 * K + 1)
      let Seven := weightedShellTowerSum_claim18440 m j (2 * K)
      Sodd ≤ R ∧ R ≤ Seven

end

end MathlibPlus.Open.Analysis.Claim18440
