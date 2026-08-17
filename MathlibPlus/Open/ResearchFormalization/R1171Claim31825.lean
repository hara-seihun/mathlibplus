import MathlibPlus.Open.ResearchFormalization.R1171Claim41590

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim31825

open MathlibPlus.Open.ResearchFormalization.R1171Claim41590

/-- Claim 31825: the generated group lies in its exact two-closure, and an
x from that generated group can replace T by T^x without changing conjugacy
of the two regular copies inside the relevant 2-closed ambient group. -/
def sylowConjugationPreservesBabaiConjugacy_claim31825 : Prop :=
  ∀ (Ω : Type*) [Fintype Ω]
    (R T X A : Subgroup (Permutation Ω)),
    regularPermutationCopy R ∧ abelianPermutationCopy R ∧
      regularPermutationCopy T ∧ abelianPermutationCopy T ∧
        X = generatedPair R T ∧ R ≤ A ∧ T ≤ A ∧ X ≤ A ∧
          twoClosedAmbient A →
      containedInOwnTwoClosure X ∧
        ∀ x : Permutation Ω, x ∈ X →
          (conjugateInAmbient A R T ↔
            conjugateInAmbient A R (conjugateSubgroup x T))

end MathlibPlus.Open.ResearchFormalization.R1171Claim31825
