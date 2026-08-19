import MathlibPlus.Open.Research.FormalizationBatch019ffedb_0225

namespace MathlibPlus.Open.ResearchFormalization.R0801Claims

open MathlibPlus.Open.Research.Batch0225

/-- Claim 24857: the exact split-one-unit partition graph on partitions of
`k + 1` is connected at every level. -/
def partitionGraphConnected_claim24857 : Prop :=
  ∀ k : ℕ, partitionGraphConnected k

/-- Claim 24861: in the equal-weight specialization `c = m`, the source
scale inequality holds on its positive natural domain, written without
truncated natural subtraction. -/
def equalWeightScaleCriterion_claim24861 : Prop :=
  ∀ (m k : ℕ), k + 1 ≤ m → m + m - k > k + 1

/-- Claim 24864: once the exact partition graph is connected, its cycle rank
is the support-edge count minus the number of partitions plus one. -/
def cycleRankFormula_claim24864 : Prop :=
  ∀ k : ℕ,
    partitionGraphConnected k →
      cycleRank k = supportSum k - partitionNumber (k + 1) + 1

end MathlibPlus.Open.ResearchFormalization.R0801Claims
