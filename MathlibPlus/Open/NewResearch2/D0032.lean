import MathlibPlus.NumberTheory.LiGram

namespace MathlibPlus.Open.NewResearch2.D0032

/-- Claim 4644: a positive-index Li sequence with zero central term has the
unique even bilateral extension used by the Li--Gram convention. -/
def evenExtensionOfLiCoefficients_claim4644 : Prop :=
  ∀ (lambdaSeq : ℕ → ℝ),
    lambdaSeq 0 = 0 →
    ∃! Λ : ℤ → ℝ,
      Λ 0 = 0 ∧
        (∀ n : ℕ, Λ (n : ℤ) = lambdaSeq n) ∧
        (∀ n : ℕ, Λ (-(n : ℤ)) = lambdaSeq n)

end MathlibPlus.Open.NewResearch2.D0032
