import MathlibPlus.Open.ResearchFormalization.Claim1171

namespace MathlibPlus.Open.ResearchFormalization.Claim1172

open MathlibPlus.Open.FormalizationBatch

/-- The exact least-start coefficient cells for the thirty literal Table 8
starts, including the predecessor-validity consequence. -/
def exactLeastStartCoefficientCells_claim1172 : Prop :=
  let table8Starts : Set ℕ :=
    {22078017, 18339738, 13026859, 12895928, 8832927, 7299254,
      7117256, 5465656, 4994010, 3462478, 3455648, 2279177,
      1529630, 1526671, 1525432, 1515074, 1200014, 1195296,
      624878, 618726, 618058, 445112, 359804, 356203, 355990,
      355177, 155935, 155907, 60297, 60224}
  ∀ x₀ : ℕ, x₀ ∈ table8Starts →
    ∀ c : ℝ, c < Real.log ((x₀ : ℝ) - 1) →
      (table8LeastIntegerStart c (x₀ : ℤ) ↔
          table8Alpha (x₀ : ℝ) < c ∧
            c ≤ table8PredecessorThreshold (x₀ : ℝ)) ∧
        (table8PredecessorThreshold (x₀ : ℝ) < c →
          c < Real.log ((x₀ : ℝ) - 1) →
            table8ValidFrom c ((x₀ : ℝ) - 1))

end MathlibPlus.Open.ResearchFormalization.Claim1172
