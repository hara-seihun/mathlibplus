import MathlibPlus.Combinatorics.Claim30192

namespace MathlibPlus.Open.ResearchFormalization.R1144Claim30195

open MathlibPlus.Combinatorics.Claim30192

noncomputable section

abbrev C7 := ZMod 7

attribute [local instance] Classical.propDecidable Classical.decEq

def nonlinearDevelopmentPermutation
    (π : Equiv.Perm C7) : Prop :=
  (¬ ∃ a b : C7, ∀ x : C7, π x = a * x + b) ∧
    ∃ B : Set C7,
      2 ≤ B.ncard ∧ B.ncard ≤ 5 ∧
      Set.image π '' translationDevelopment B =
        translationDevelopment (Set.image π B)

/-- Claim 30195: exactly 588 of the 5040 point permutations of `C₇` are
    nonaffine permutations carrying some complete 2--5 point development to
    the development of its image. -/
def exactNonlinearDevelopmentCensus_claim30195 : Prop :=
  Fintype.card (Equiv.Perm C7) = 5040 ∧
    ((Finset.univ : Finset (Equiv.Perm C7)).filter
      nonlinearDevelopmentPermutation).card = 588

end

end MathlibPlus.Open.ResearchFormalization.R1144Claim30195
