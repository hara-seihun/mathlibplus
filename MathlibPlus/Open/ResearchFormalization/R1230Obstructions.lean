import MathlibPlus.Open.ResearchFormalization.R1230

namespace MathlibPlus.Open.ResearchFormalization.R1230Obstructions

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1230

/-- Claim 30381: the actual center-rooted depth-two-spider coefficient
polynomials have no common complex root, equivalently their gcd in
`Q[x]` is one, throughout the admissible order range. -/
def commonRootObstruction_claim30381 : Prop :=
  ∀ (a b : ℕ),
    3 ≤ spiderOrder a b →
      (∀ α : ℂ,
        (evalComplex α (spiderA a b) = 0 ∧
          evalComplex α (spiderB a b) = 0) → False) ∧
        gcd (spiderA a b) (spiderB a b) = 1

end

end MathlibPlus.Open.ResearchFormalization.R1230Obstructions
