import MathlibPlus.Open.ResearchFormalization.R0307TreeClaim19597

namespace MathlibPlus.Open.ResearchFormalization.R0307Claim19609

noncomputable section

open MathlibPlus.Open.Combinatorics

/-- Claim 19609: on the exact order-one and order-two tree-supported graph
spaces, the boundary compositions are both twice the identity, and the two
boundary maps are bijective with zero kernel and one-dimensional range. -/
def claim19609 : Prop :=
  (∀ x : GraphSpace 1, x ∈ treeSpace 1 →
    L 1 (G 1 x) = (2 : ℚ) • x) ∧
  (∀ y : GraphSpace 2, y ∈ treeSpace 2 →
    G 1 (L 1 y) = (2 : ℚ) • y) ∧
  (∀ x : GraphSpace 1, x ∈ treeSpace 1 → G 1 x ∈ treeSpace 2) ∧
  (∀ y : GraphSpace 2, y ∈ treeSpace 2 → L 1 y ∈ treeSpace 1) ∧
  (∀ y : GraphSpace 2, y ∈ treeSpace 2 →
    ∃! x : GraphSpace 1, x ∈ treeSpace 1 ∧ G 1 x = y) ∧
  (∀ x : GraphSpace 1, x ∈ treeSpace 1 →
    ∃! y : GraphSpace 2, y ∈ treeSpace 2 ∧ L 1 y = x) ∧
  (∀ x : GraphSpace 1, x ∈ treeSpace 1 → G 1 x = 0 → x = 0) ∧
  (∀ y : GraphSpace 2, y ∈ treeSpace 2 → L 1 y = 0 → y = 0) ∧
  Module.finrank ℚ (Submodule.map (G 1) (treeSpace 1)) = 1 ∧
  Module.finrank ℚ (Submodule.map (L 1) (treeSpace 2)) = 1

end

end MathlibPlus.Open.ResearchFormalization.R0307Claim19609
