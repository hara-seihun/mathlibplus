import MathlibPlus.Open.FormalizationBatch.AdmittedClaims1158And1166

namespace MathlibPlus.Open.ResearchFormalization.Claim1171

open MathlibPlus.Open.FormalizationBatch

/-- Claim 1171: every literal Table 8 start is composite, its predecessor
shares the start's prime count, and the score has the displayed negative
interior derivative on that predecessor plateau. -/
def claim1171 : Prop :=
  let table8Starts : Set ℕ :=
    {22078017, 18339738, 13026859, 12895928, 8832927, 7299254,
      7117256, 5465656, 4994010, 3462478, 3455648, 2279177,
      1529630, 1526671, 1525432, 1515074, 1200014, 1195296,
      624878, 618726, 618058, 445112, 359804, 356203, 355990,
      355177, 155935, 155907, 60297, 60224}
  ∀ x₀ : ℕ, x₀ ∈ table8Starts →
    ¬ Nat.Prime x₀ ∧
      ∃ n₀ : ℕ,
        table8PrimeCount ((x₀ : ℝ) - 1) = (n₀ : ℝ) ∧
          table8PrimeCount (x₀ : ℝ) = (n₀ : ℝ) ∧
            (x₀ : ℝ) - 1 > (n₀ : ℝ) ∧
              (∀ x : ℝ,
                x ∈ Set.Ico ((x₀ : ℝ) - 1) (x₀ : ℝ) →
                  table8PrimeCount x = (n₀ : ℝ)) ∧
                (∀ x : ℝ,
                  x ∈ Set.Ioo ((x₀ : ℝ) - 1) (x₀ : ℝ) →
                    HasDerivAt table8Score
                      (1 / x - 1 / (n₀ : ℝ)) x ∧
                      1 / x - 1 / (n₀ : ℝ) < 0)

end MathlibPlus.Open.ResearchFormalization.Claim1171
