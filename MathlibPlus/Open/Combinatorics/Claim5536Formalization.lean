import MathlibPlus.Open.Combinatorics.Claim5539Formalization

namespace MathlibPlus.Open.Combinatorics.Claim5536

open MathlibPlus.Open.Combinatorics.Claim5539Formalization

/-- The row-choice game is represented by the least attractor generated from
empty winning set: a column is winning exactly when an incident row has only
competitors that are winning.  The support and the finite-wave carrier are
those of the reviewed matrix formalization. -/
def rowChoiceAttractorGame_claim5536 : Prop :=
  ∀ {K R C : Type*} [Field K] [Fintype R] [Fintype C]
    (A : Matrix R C K) (c : C),
    (∃ k : ℕ, c ∈ singletonPeelingWave A k) ↔
      ∃ r : R,
        A r c ≠ 0 ∧
          ∀ d : C,
            d ∈ rowSupport A r \ {c} →
              ∃ k : ℕ, d ∈ singletonPeelingWave A k

end MathlibPlus.Open.Combinatorics.Claim5536
