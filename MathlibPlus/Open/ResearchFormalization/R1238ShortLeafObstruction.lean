import MathlibPlus.Open.Research.R1238

namespace MathlibPlus.Open.ResearchFormalization.R1238ShortLeafObstruction

noncomputable section

open Polynomial
open MathlibPlus.Open.Research.R1238

/-- Claim 30449: retain the common-root bridge for the actual short-leaf
`A_{a,b}` and `B_{a,b}` carriers before making the shift `t = α + 1` to the
quartic. -/
def commonRootImpliesShiftedQuartic_claim30449 : Prop :=
  ∀ (a b : ℕ),
    1 ≤ a →
      ∀ α : ℂ,
        (Polynomial.eval₂ (algebraMap ℚ ℂ) α (shortLeafA a b) = 0 ∧
          Polynomial.eval₂ (algebraMap ℚ ℂ) α (shortLeafB a b) = 0) →
          let d : ℕ := a + b
          let t : ℂ := α + 1
          α * (α + 1) ^ 3 + (d : ℂ) * (α + 1) - 1 = 0 ∧
            t ^ 4 - t ^ 3 + (d : ℂ) * t - 1 = 0

end

end MathlibPlus.Open.ResearchFormalization.R1238ShortLeafObstruction
