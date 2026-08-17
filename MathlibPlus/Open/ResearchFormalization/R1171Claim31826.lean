import MathlibPlus.Open.ResearchFormalization.R1171Claim41591

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim31826

open MathlibPlus.Open.ResearchFormalization.R1171Claim41591

/-- Claim 31826: an element of the actual normalizer can align the induced
quotient copies; the aligned copies contain the same literal D, have identity
normalized quotient action, and differ only by D-valued translations. -/
def markedQuotientAlignmentLeavesDValuedBlockTranslation_claim31826 : Prop :=
  ∀ (Ω : Type*) [Fintype Ω] (p n : ℕ)
    (A P R S D : Subgroup (Permutation Ω))
    (blocks : Set (Set Ω)),
    Nat.Prime p → 1 ≤ n →
      P ≤ A ∧ R ≤ P ∧ S ≤ P ∧
        regularPermutationCopy R ∧ abelianPermutationCopy R ∧
          regularPermutationCopy S ∧ abelianPermutationCopy S ∧
            IsPGroup p R ∧ IsPGroup p S ∧
              hasElementaryAbelianType R p n ∧
                hasElementaryAbelianType S p n ∧
                  centralInAmbient P D ∧ Nat.card D = p ∧
                    D ≤ R ∧ D ≤ S ∧ dOrbitBlockSystem D P blocks →
      ∀ a : normalizerWithin A D,
        quotientBlockConjugates (a : Permutation Ω) R S blocks →
          D ≤ conjugateSubgroup (a : Permutation Ω) R ∧
            ∃ φ : conjugateSubgroup (a : Permutation Ω) R ≃* S,
              normalizedDValuedBlockTranslation
                (conjugateSubgroup (a : Permutation Ω) R) S D blocks φ

end MathlibPlus.Open.ResearchFormalization.R1171Claim31826
