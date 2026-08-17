import MathlibPlus.Combinatorics.Claim30192

namespace MathlibPlus.Open.ResearchFormalization.R1144Claim30194

open MathlibPlus.Combinatorics.Claim30192

noncomputable section

abbrev C7 := ZMod 7

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Claim 30194: the exact nonlinear-development predicate on point
    permutations of `C₇`. -/
def nonlinearDevelopmentPermutation_claim30194
    (π : Equiv.Perm C7) : Prop :=
  (¬ ∃ a b : C7, ∀ x : C7, π x = a * x + b) ∧
    ∃ B : Set C7,
      2 ≤ B.ncard ∧ B.ncard ≤ 5 ∧
      Set.image π '' translationDevelopment B =
        translationDevelopment (Set.image π B)

end

end MathlibPlus.Open.ResearchFormalization.R1144Claim30194
