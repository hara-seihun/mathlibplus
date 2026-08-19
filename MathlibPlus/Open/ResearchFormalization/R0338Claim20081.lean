import MathlibPlus.Open.Research.R0338QuadraticDeck

namespace MathlibPlus.Open.ResearchFormalization.R0338Claim20081

open MathlibPlus.Open.Research.R0338

/-- Claim 20081: the exact realized unlabeled-tree counts and quadratic-feature
space dimensions through order eleven. -/
def exactQuadraticFeatureDimensions_claim20081 : Prop :=
  (realizedTrees 4).card = 2 ∧
    Module.finrank ℚ (quadraticFeatureSpace 4) = 2 ∧
    (realizedTrees 5).card = 3 ∧
    Module.finrank ℚ (quadraticFeatureSpace 5) = 3 ∧
    (realizedTrees 6).card = 6 ∧
    Module.finrank ℚ (quadraticFeatureSpace 6) = 6 ∧
    (realizedTrees 7).card = 11 ∧
    Module.finrank ℚ (quadraticFeatureSpace 7) = 11 ∧
    (realizedTrees 8).card = 23 ∧
    Module.finrank ℚ (quadraticFeatureSpace 8) = 23 ∧
    (realizedTrees 9).card = 47 ∧
    Module.finrank ℚ (quadraticFeatureSpace 9) = 47 ∧
    (realizedTrees 10).card = 106 ∧
    Module.finrank ℚ (quadraticFeatureSpace 10) = 106 ∧
    (realizedTrees 11).card = 235 ∧
    Module.finrank ℚ (quadraticFeatureSpace 11) = 234

end MathlibPlus.Open.ResearchFormalization.R0338Claim20081
