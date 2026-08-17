import MathlibPlus.Open.Combinatorics.TreeDeck

namespace MathlibPlus.Open.ResearchFormalizationD0079

open ProjectsResearch.TreeDeck

/-- Claim 5077: for every redundancy parameter and tree-state degree, the
block map is the componentwise stack of the leaf deck after each diagonal
connected-tree-motif observable in the exact edge-count range. -/
def redundancyQAttachmentObservabilityMap_claim5077 : Prop :=
  ∀ (q n : ℕ) (x : TreeState n) (H : MotifIndex q),
    (observabilityMap n q x) H =
      (leafDeck n) ((motifDiagonal H.1.2 n) x)

end MathlibPlus.Open.ResearchFormalizationD0079
